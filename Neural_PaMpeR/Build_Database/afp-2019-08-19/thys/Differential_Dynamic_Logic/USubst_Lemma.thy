theory "USubst_Lemma"
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Frechet_Correctness"
  "Static_Semantics"
  "Coincidence"
  "Bound_Effect"
  "USubst"
begin context ids begin
section \<open>Soundness proof for uniform substitution rule\<close>
lemma interp_eq:
  "f = f' \<Longrightarrow> p = p' \<Longrightarrow> c = c' \<Longrightarrow> PP = PP' \<Longrightarrow> ode = ode' \<Longrightarrow> odebv = odebv' \<Longrightarrow>
   \<lparr>Functions = f, Predicates = p, Contexts = c, Programs = PP, ODEs = ode, ODEBV = odebv\<rparr> =
   \<lparr>Functions = f', Predicates = p', Contexts = c', Programs = PP', ODEs = ode', ODEBV = odebv'\<rparr>"
  by auto

subsection \<open>Lemmas about well-formedness of (adjoint) interpretations.\<close>

text \<open>When adding a function to an interpretation with {\tt extendf}, we need to show it's C1 continuous.
  We do this by explicitly constructing the derivative {\tt extendf\_deriv} and showing it's continuous.\<close>
primrec extendf_deriv :: "('sf,'sc,'sz) interp \<Rightarrow> 'sf \<Rightarrow> ('sf + 'sz,'sz) trm \<Rightarrow> 'sz state \<Rightarrow> 'sz Rvec \<Rightarrow> ('sz Rvec \<Rightarrow> real)"
where
  "extendf_deriv I _ (Var i) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I _ (Const r) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I g (Function f args) \<nu> x =
  (case f of 
    Inl ff \<Rightarrow> (THE f'. \<forall>y. (Functions I ff has_derivative f' y) (at y))
              (\<chi> i. dterm_sem
                     \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                        ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                     (args i) \<nu>) \<circ>
             (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I g (args ia) \<nu> x \<nu>')
  | Inr ff \<Rightarrow> (\<lambda> \<nu>'. \<nu>' $ ff))"
| "extendf_deriv I g (Plus t1 t2) \<nu> x = (\<lambda>\<nu>'. (extendf_deriv I g t1 \<nu> x \<nu>') + (extendf_deriv I g t2 \<nu> x \<nu>'))"
| "extendf_deriv I g (Times t1 t2) \<nu> x = 
   (\<lambda>\<nu>'. ((dterm_sem (extendf I x) t1 \<nu> * (extendf_deriv I g t2 \<nu> x \<nu>'))) 
       + (extendf_deriv I g t1 \<nu> x \<nu>') * (dterm_sem (extendf I x) t2 \<nu>))"
| "extendf_deriv I g ($' _) \<nu> = undefined"
| "extendf_deriv I g (Differential _) \<nu> = undefined"

lemma extendf_dterm_sem_continuous:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "continuous_on UNIV (\<lambda>x. dterm_sem (extendf I x) f' \<nu>)"
proof(induction rule: dfree.induct[OF free])
  case (3 args f)
  then show ?case 
    apply(cases f)
     apply (auto simp add: continuous_intros)
    subgoal for a
      apply(rule continuous_on_compose2[of UNIV "Functions I a" UNIV "(\<lambda> x. (\<chi> i. dterm_sem
                       \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                       (args i) \<nu>))"])
      subgoal
        using is_interpD[OF good_interp]
        using has_derivative_continuous_on[of UNIV "(Functions I a)" "(THE f'. \<forall>x. (Functions I a has_derivative f' x) (at x))"] 
        by auto
      apply(rule continuous_on_vec_lambda) by auto
    done
qed (auto simp add: continuous_intros)

lemma extendf_deriv_bounded:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "bounded_linear (extendf_deriv I i f' \<nu> x)"
proof(induction rule: dfree.induct[OF free])
  case (1 i)
  then show ?case by auto
next
  case (2 r)
  then show ?case by auto
next
  case (3 args f)
  then show ?case apply auto
    apply(cases f)
     apply auto
    subgoal for a
      apply(rule bounded_linear_compose[of "(THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
           (\<chi> i. dterm_sem
                  \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                  (args i) \<nu>)"])
       subgoal using good_interp unfolding is_interp_def  using has_derivative_bounded_linear  by fastforce
      apply(rule bounded_linear_vec)
      by auto
    done
next
  case (4 \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case apply auto
    using bounded_linear_add by blast
next
  case (5 \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case apply auto
    apply(rule bounded_linear_add)
     apply(rule bounded_linear_const_mult)
     subgoal by auto
    apply(rule bounded_linear_mult_const)
    subgoal by auto
    done
qed

lemma extendf_deriv_continuous:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i f' \<nu> x))"
proof (induction rule: dfree.induct[OF free])
  case (3 args f)
  assume dfrees:"\<And>i. dfree (args i)"
  assume const:"\<And>j. continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i (args j) \<nu> x))"
  then show ?case 
    unfolding extendf_deriv.simps
    apply(cases f)
    subgoal for a 
      apply simp
      proof -
        have boundedF:"\<And>x. bounded_linear (((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) ))"
          using blinfun.bounded_linear_right using good_interp unfolding is_interp_def 
          by auto
        have boundedG:"\<And>x. bounded_linear (\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))"
          by (simp add: bounded_linear_vec dfrees extendf_deriv_bounded good_interp)
        have boundedH:"\<And>x. bounded_linear (\<lambda>b. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem
                          (extendf I x)
                                 
                                 (args i) \<nu>)
                          (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))"
          using bounded_linear_compose  boundedG boundedF by blast
        have eq:"(\<lambda>x. Blinfun (\<lambda>b. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem
                                 (extendf I x)
                                 (args i) \<nu>)
                          (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b)))
                          = 
                (\<lambda>x. blinfun_compose(Blinfun((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem
                                 (extendf I x)
                                 (args i) \<nu>) )) (Blinfun(\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))))"
          apply(rule ext)
          apply(rule blinfun_eqI)
          subgoal for x ia
            using boundedG[of x]  blinfun_apply_blinfun_compose bounded_linear_Blinfun_apply
          proof -
            have f1: "bounded_linear (\<lambda>v. FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))"
              using FunctionFrechet.simps \<open>bounded_linear (\<lambda>b. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))\<close>
              by fastforce          
            have "bounded_linear (FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))"
              using good_interp is_interp_def by blast
            then have "blinfun_apply (Blinfun (FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))) (\<chi> s. extendf_deriv I i (args s) \<nu> x ia) = blinfun_apply (Blinfun (\<lambda>v. FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))) ia"
              using f1 by (simp add: bounded_linear_Blinfun_apply)
            then have "blinfun_apply (Blinfun (FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))) (\<chi> s. extendf_deriv I i (args s) \<nu> x ia) = blinfun_apply (Blinfun (\<lambda>v. FunctionFrechet I a (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))) ia \<and> bounded_linear (\<lambda>v. \<chi> s. extendf_deriv I i (args s) \<nu> x v)"
              by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>) (* failed *)
            then show ?thesis
              by (simp add: bounded_linear_Blinfun_apply)
          qed
        done
        have bounds:"\<And>ia x. bounded_linear (extendf_deriv I i (args ia) \<nu> x)" 
          by (simp add: dfrees extendf_deriv_bounded good_interp)
        have vec_bound:"\<And>x. bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)" 
          by (simp add: boundedG)
        have blinfun_vec:"(\<lambda>x. Blinfun (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)) = (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
          apply(rule ext)
          apply(rule blinfun_eqI)
          apply(rule vec_extensionality)
          subgoal for x y ia
          proof -
            have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia"
              by (simp add: bounded_linear_Blinfun_apply bounds)
            then have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia \<and> bounded_linear (\<lambda>v. \<chi> s. extendf_deriv I i (args s) \<nu> x v)"
              by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>)
            then show ?thesis
              by (simp add: bounded_linear_Blinfun_apply)
          qed
          done
        have vec_cont:"continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
          apply(rule continuous_blinfun_vec')
          using "3.IH" by blast
        have cont_intro:"\<And> f g s. continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x  o\<^sub>L  g x)"
          by(auto intro: continuous_intros)
        have cont:"continuous_on UNIV (\<lambda>x. blinfun_compose(Blinfun((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem
                                 \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                    Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                                 (args i) \<nu>) )) (Blinfun(\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))))"
          apply(rule cont_intro)
           defer
           subgoal using blinfun_vec vec_cont by presburger
          apply(rule continuous_on_compose2[of UNIV "(\<lambda>x. Blinfun ((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y)) x))"])
            subgoal using good_interp unfolding is_interp_def by simp
           apply(rule continuous_on_vec_lambda)
           subgoal for i using extendf_dterm_sem_continuous[OF dfrees[of i] good_interp] by auto
          by auto
        then show " continuous_on UNIV
       (\<lambda>x. Blinfun (\<lambda>b. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                          (\<chi> i. dterm_sem
                                 \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                    Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                                 (args i) \<nu>)
                          (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b)))"
          using eq apply simp by presburger
        qed
    by simp
next
  case (4 \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  assume IH1:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x))"
  assume IH2:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x))"
  have bound:"\<And>x. bounded_linear  (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a + extendf_deriv I i \<theta>\<^sub>2 \<nu> x a)"
    using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp]
    by (simp add: bounded_linear_add)
  have eq:"(\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a + extendf_deriv I i \<theta>\<^sub>2 \<nu> x a)) = (\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) + Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    subgoal for x j
      using bound[of x] extendf_deriv_bounded[OF free1 good_interp] 
      extendf_deriv_bounded[OF free2 good_interp] 
      blinfun.add_left[of "Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)" "Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "(extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "(extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      by (simp add: bounded_linear_Blinfun_apply)
    done
  have "continuous_on UNIV (\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) + Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a))"
    apply(rule continuous_intros)
    using IH1 IH2 by auto
  then show ?case
    apply simp
    using eq by presburger
next
  case (5 \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  assume IH1:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x))"
  assume IH2:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x))"
  have bounded:"\<And>x. bounded_linear (\<lambda>a. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> * extendf_deriv I i \<theta>\<^sub>2 \<nu> x a +
                       extendf_deriv I i \<theta>\<^sub>1 \<nu> x a * dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu>)"
    using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp]
    by (simp add: bounded_linear_add bounded_linear_const_mult bounded_linear_mult_const)
  have eq:"(\<lambda>x. Blinfun (\<lambda>a. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> * extendf_deriv I i \<theta>\<^sub>2 \<nu> x a +
                       extendf_deriv I i \<theta>\<^sub>1 \<nu> x a * dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu>)) = 
           (\<lambda>x. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a) +
           dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    subgoal for x j
      using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp] bounded[of x]
      blinfun.scaleR_left 
      bounded_linear_Blinfun_apply[of "Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      mult.commute 
      plus_blinfun.rep_eq[of "dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)" "dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      real_scaleR_def
      by (simp add: blinfun.scaleR_left bounded_linear_Blinfun_apply)
    done
  have "continuous_on UNIV (\<lambda>x. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a) +
           dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a))"
    apply(rule continuous_intros)+
      apply(rule extendf_dterm_sem_continuous[OF free1 good_interp])
     apply(rule IH2)
    apply(rule continuous_intros)+
     apply(rule extendf_dterm_sem_continuous[OF free2 good_interp])
    by(rule IH1)
  then show ?case
    unfolding extendf_deriv.simps
    using eq by presburger
qed (auto intro: continuous_intros)
  
lemma extendf_deriv:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (extendf_deriv I i_f f' \<nu> x)) (at x)"
  using free apply (induction rule: dfree.induct)
  apply(auto)+
   defer
   subgoal for \<theta>\<^sub>1 \<theta>\<^sub>2 x
     apply(rule has_derivative_mult)
      by auto
   subgoal for args i x
     apply(cases "i")
      defer
      apply auto
      subgoal for b using has_derivative_proj' by blast
     subgoal for a
   proof -
     assume dfrees:"(\<And>i. dfree (args i))"
     assume IH1:"(\<And>ia. \<forall>x. ((\<lambda>R. dterm_sem
                      \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                         ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                      (args ia) \<nu>) has_derivative
                extendf_deriv I i_f (args ia) \<nu> x)
                (at x))"
     then have IH1':"(\<And>ia. \<And>x. ((\<lambda>R. dterm_sem
                      \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                         ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                      (args ia) \<nu>) has_derivative
                extendf_deriv I i_f (args ia) \<nu> x)
                (at x))"
       by auto
     assume a:"i = Inl a"
     have chain:"\<And>f f' x s g g'. (f has_derivative f') (at x within s) \<Longrightarrow>
      (g has_derivative g') (at (f x) within f ` s) \<Longrightarrow> (g \<circ> f has_derivative g' \<circ> f') (at x within s)"
       by (auto intro: derivative_intros)
     let ?f = "(\<lambda>x. Functions I a x)"
     let ?g = "(\<lambda> R. (\<chi> i. dterm_sem
                       \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                       (args i) \<nu>))"
     let ?myf' = "(\<lambda>x. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y)) (?g x))"
     let ?myg' = "(\<lambda>x. (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))"
     have fg_eq:"(\<lambda>R. Functions I a
           (\<chi> i. dterm_sem
                  \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                  (args i) \<nu>)) = (?f \<circ> ?g)"
       by auto
     have "\<forall>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)"
       apply (rule allI)
       apply (rule diff_chain_at)
       subgoal for xa
         apply (rule has_derivative_vec)
         subgoal for i using IH1'[of i xa] by auto
         done
       subgoal for xa 
       proof -
         have deriv:"\<And>x. (Functions I a has_derivative FunctionFrechet I a x) (at x)"
         and cont:"continuous_on UNIV (\<lambda>x. Blinfun (FunctionFrechet I a x))"
           using good_interp[unfolded is_interp_def] by auto
         show ?thesis
           apply(rule has_derivative_at_withinI)
           using deriv by auto
       qed
      done
    then have "((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)" by auto
    then show "((\<lambda>R. Functions I a
           (\<chi> i. dterm_sem
                  \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                  (args i) \<nu>)) has_derivative
              (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
      (\<chi> i. dterm_sem
             \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
             (args i) \<nu>) \<circ>
     (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))
     (at x) "
      using fg_eq by auto
  qed
  done
done

lemma adjoint_safe:
  assumes good_interp:"is_interp I"
  assumes good_subst:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') "    
  shows "is_interp (adjoint I \<sigma> \<nu>)"
  apply(unfold adjoint_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps)
   subgoal for x i
     apply(cases "SFunctions \<sigma> i = None")
      subgoal
        apply(auto simp del: extendf.simps extendc.simps)
        using good_interp unfolding is_interp_def by simp
      apply(auto  simp del: extendf.simps extendc.simps)
      subgoal for f'
        using good_subst[of i f'] apply (auto  simp del: extendf.simps extendc.simps)
      proof -
        assume some:"SFunctions \<sigma> i = Some f'"
        assume free:"dfree f'"
        let ?f = "(\<lambda>R. dterm_sem (extendf I R) f' \<nu>)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="extendf_deriv I i f' \<nu>"
        have Pf:"?Pred ?f''"
          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]
          by auto
        have "(THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          using Pf the_all_deriv by auto
        show "((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative f'a x) (at x)) x) (at x)"
          using the_eq Pf by simp
      qed
      done
    subgoal for i
      apply(cases "SFunctions \<sigma> i = None")
       subgoal
         apply(auto  simp del: extendf.simps extendc.simps)
         using good_interp unfolding is_interp_def by simp
      apply(auto  simp del: extendf.simps extendc.simps)
      subgoal for f'
        using good_subst[of i f'] apply (auto  simp del: extendf.simps extendc.simps)
      proof -
        assume some:"SFunctions \<sigma> i = Some f'"
        assume free:"dfree f'"
        let ?f = "(\<lambda>R. dterm_sem (extendf I R) f' \<nu>)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="extendf_deriv I i f' \<nu>"
        have Pf:"?Pred ?f''"
          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]
          by auto
        have "\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          using Pf the_all_deriv by auto
        have "continuous_on UNIV (\<lambda>x. Blinfun (?f'' x))"
          by(rule extendf_deriv_continuous[OF free good_interp])
        show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'a. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative f'a x) (at x)) x))"
          using the_eq Pf 
          by (simp add: \<open>continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i f' \<nu> x))\<close>)
      qed
    done
  done

lemma adjointFO_safe:
  assumes good_interp:"is_interp I"
  assumes good_subst:"(\<And>i. dsafe (\<sigma> i))"
  shows "is_interp (adjointFO I \<sigma> \<nu>)"
  apply(unfold adjointFO_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps)
   subgoal for x i
     apply(cases "i")
      subgoal
        apply(auto  simp del: extendf.simps extendc.simps)
        using good_interp unfolding is_interp_def by simp
     apply(auto  simp del: extendf.simps extendc.simps)
     subgoal for f'
     proof -
       assume some:"i = Inr f'"
       have free:"dsafe (\<sigma> f')" using good_subst by auto
       let ?f = "(\<lambda>_. dterm_sem I (\<sigma> f') \<nu>)"
       let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
       let ?f''="(\<lambda>_ _. 0)"
       have Pf:"?Pred ?f''"
       proof (induction "\<sigma> f'")
       qed (auto)
       have "(THE G. (?f has_derivative G) (at x)) = ?f'' x"
         apply(rule the_deriv)
         using Pf by auto
       then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
         using Pf the_all_deriv[of ?f ?f''] by auto
       have another_eq:"(THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x = (\<lambda> _. 0)"
         using Pf by (simp add: the_eq) 
       then show "((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x) (at x)"
         using the_eq Pf by simp
       qed
    done
  subgoal for i
    apply(cases i)
     subgoal
       apply(auto  simp del: extendf.simps extendc.simps)
       using good_interp unfolding is_interp_def by simp
    apply(auto  simp del: extendf.simps extendc.simps)
    subgoal for f'
      using good_subst[of f'] 
    proof -
      assume some:"i = Inr f'"
      have free:"dsafe (\<sigma> f')" using good_subst by auto
      let ?f = "(\<lambda>R. dterm_sem I (\<sigma> f') \<nu>)"
      let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
      let ?f''="(\<lambda>_ _. 0)" (* *)
      have Pf:"?Pred ?f''" by simp
      have "\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
        apply(rule the_deriv)
        using Pf by auto
      then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
        using Pf the_all_deriv[of "(\<lambda>R. dterm_sem I (\<sigma> f') \<nu>)" "(\<lambda>_ _. 0)"]
        by blast
      then have blin_cont:"continuous_on UNIV (\<lambda>x. Blinfun (?f'' x))"
        by (simp add: continuous_on_const)
      have truth:"(\<lambda>x. Blinfun ((THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x))
        = (\<lambda>x. Blinfun (\<lambda> _. 0))"
        apply(rule ext)
        apply(rule blinfun_eqI)
        by (simp add: local.the_eq)
      then show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x))"
        using truth 
        by (metis (mono_tags, lifting) blin_cont continuous_on_eq)
      qed
    done
  done

subsection \<open>Lemmas about adjoint interpretations\<close>
lemma adjoint_consequence:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> (\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f') \<Longrightarrow> Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> adjoint I \<sigma> \<nu> = adjoint I \<sigma> \<omega>"
  apply(unfold FVS_def)
  apply(auto)
  apply(unfold adjoint_def)
  apply(rule interp_eq)
       apply(auto simp add: fun_eq_iff)
    subgoal for xa xaa 
      apply(cases "SFunctions \<sigma> xa")
       apply(auto)
      subgoal for a 
      proof -
        assume safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SFunctions \<sigma> xa = Some a"
        from safes some have safe:"dsafe a" by auto
        have sub:"SFV \<sigma> (Inl xa) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inl xa))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVT a)"
          using some by auto
        show "?thesis"
          using coincidence_dterm[of a, OF safes[of xa a, OF some] agree] by auto
      qed
    done
   subgoal for xa xaa 
    apply(cases "SPredicates \<sigma> xa")
     apply(auto)
    subgoal for a 
    proof -
      assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
      assume some:"SPredicates \<sigma> xa = Some a"
      assume sem:"\<nu> \<in> fml_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                  ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
        a"
      from safes some have safe:"fsafe a" by auto
      have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
        by blast
      from agrees 
      have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
        using agree_sub[OF sub agrees] by auto
      then have agree:"Vagree \<nu> \<omega> (FVF a)"
        using some by auto
      let ?I' = "\<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                  ODEs = ODEs I, ODEBV = ODEBV I\<rparr>"
      have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto
      show "?thesis"
        using coincidence_formula[of a, OF safes[of xa a, OF some] IA agree] sem by auto
    qed
    done
   subgoal for xa xaa 
    apply(cases "SPredicates \<sigma> xa")
     apply(auto)
    subgoal for a 
    proof -
      assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
      assume some:"SPredicates \<sigma> xa = Some a"
      assume sem:"\<omega> \<in> fml_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                  ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
        a"
      from safes some have safe:"fsafe a" by auto
      have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
        by blast
      from agrees 
      have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
        using agree_sub[OF sub agrees] by auto
      then have agree:"Vagree \<nu> \<omega> (FVF a)"
        using some by auto
      let ?I' = "\<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                  ODEs = ODEs I, ODEBV = ODEBV I\<rparr>"
      have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto
      show "?thesis"
        using coincidence_formula[of a, OF safes[of xa a, OF some] IA agree] sem by auto
    qed
  done    
done

lemma SIGT_plus1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_plus2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_times1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_times2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma uadmit_sterm_adjoint':
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  case (Times \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"    
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  case (Function x1a x2a)
  assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT x. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
    sterm_sem (local.adjoint I \<sigma> \<nu>) x = sterm_sem (local.adjoint I \<sigma> \<omega>) x"
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
    sterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) = sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j)"
    using rangeI by auto
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    unfolding Vagree_def SIGT.simps using rangeI by blast
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    using SIGT by auto
  have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
     defer
     subgoal for x a
     proof -
       assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
       assume sems:"(\<And>j. \<forall>x. sterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) x = sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j) x)"
       assume some:"SFunctions \<sigma> x1a = Some a"
       note FVT = VAf[OF some]
       have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
         using coincidence_dterm[OF dsafe[OF some] FVT] by auto
       have "\<And>R. Functions (local.adjoint I \<sigma> \<nu>) x1a R = Functions (local.adjoint I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjoint_def by auto
       then show "Functions (local.adjoint I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) x) =
                 Functions (local.adjoint I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) x)"
         by auto
     qed
    unfolding adjoint_def apply auto    
    done
qed (auto)  
  
\<comment> \<open>Not used, but good practice for \<open>dterm\<close> adjoint\<close>
lemma uadmit_sterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding TUadmit_def by auto
  then have sub1:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_sterm_adjoint'[OF dsafe fsafe VA'] by auto
qed

lemma uadmit_sterm_ntadjoint':
  assumes dsafe:"\<And>i. dsafe (\<sigma> i)"
  shows  "Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
  from VA 
    have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and  VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1[OF VA1] IH2[OF VA2] by auto
next
  case (Times \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
  from VA 
  have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
  and  VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1[OF VA1] IH2[OF VA2] by auto
next
  case (Function x1a x2a) 
  assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
    sterm_sem (adjointFO I \<sigma> \<nu>) x = sterm_sem (adjointFO I \<sigma> \<omega>) x"
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
    sterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) = sterm_sem (adjointFO I \<sigma> \<omega>) (x2a j)"
    using rangeI by auto
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i)) "
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
    unfolding Vagree_def SIGT.simps using rangeI by blast
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. x1a = Inr a \<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    using SIGT by auto
  have VAf:"\<And>a. x1a = Inr a \<Longrightarrow>Vagree \<nu> \<omega> (FVT (\<sigma> a))"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "x1a")
     defer
     subgoal for x a
     proof -
       assume VA:"(\<And>a.  x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))"
       assume sems:"(\<And>j. \<forall>x. sterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) x = sterm_sem (adjointFO I \<sigma> \<omega>) (x2a j) x)"
       assume some:"x1a = Inr a"
       note FVT = VAf[OF some]
       from dsafe have dsafer:"\<And>i. dsafe (\<sigma> i)" using dfree_is_dsafe by auto
       have dsem:"dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
         using coincidence_dterm[OF dsafer FVT] some by auto
       then have "\<And>R. Functions (adjointFO I \<sigma> \<nu>) x1a R = Functions (adjointFO I \<sigma> \<omega>) x1a R"
         using some unfolding adjoint_def unfolding adjointFO_def by auto
       then show "Functions (adjointFO I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) x) =
                  Functions (adjointFO I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) x)"
         by auto
     qed
    unfolding adjointFO_def by auto
qed (auto) 
  
lemma uadmit_sterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>i . dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows  "sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> ((\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding NTUadmit_def by auto
  then have sub1:"(\<Union>i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_sterm_ntadjoint'[OF  dsafe VA'] by auto
qed

lemma uadmit_dterm_adjoint':
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  case (Times \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  case (Function x1a x2a)
  assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT x. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
    dsafe x \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) x = dterm_sem (local.adjoint I \<sigma> \<omega>) x"
  assume safe:"dsafe (Function x1a x2a)"
  from safe have safes:"\<And>j. dsafe (x2a j)" by auto
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
    dterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j)"
    using rangeI safes by auto
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    unfolding Vagree_def SIGT.simps using rangeI by blast
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    using SIGT by auto
  have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
     defer
     subgoal for x1 x2 a
     proof -
       assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
       assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j) (x1,x2))"
       assume some:"SFunctions \<sigma> x1a = Some a"
       note FVT = VAf[OF some]
       have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
         using dfree dfree_is_dsafe by auto
       have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
         using coincidence_dterm[OF dsafe[OF some] FVT] by auto
       have "\<And>R. Functions (local.adjoint I \<sigma> \<nu>) x1a R = Functions (local.adjoint I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjoint_def by auto
       then show "Functions (local.adjoint I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                  Functions (local.adjoint I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) (x1,x2))"
         by auto
      qed
  unfolding adjoint_def apply auto    
  done
next
  case (Differential \<theta>)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>"
  assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Differential \<theta>). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  assume safe:"dsafe (Differential \<theta>)"
  then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
  from VA have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    by auto
  have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
    using dfree dfree_is_dsafe by auto
  have sem:"sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>"
    using uadmit_sterm_adjoint'[OF dsafe fsafe VA', of "\<lambda> x y. x" "\<lambda> x y. x" I] by auto
  have good1:"is_interp (adjoint I \<sigma> \<nu>)" using adjoint_safe[OF good_interp dfree] by auto
  have good2:"is_interp (adjoint I \<sigma> \<omega>)" using adjoint_safe[OF good_interp dfree] by auto
  have frech:"frechet (local.adjoint I \<sigma> \<nu>) \<theta> = frechet (local.adjoint I \<sigma> \<omega>) \<theta>"
    apply (auto simp add: fun_eq_iff)
    subgoal for a b
      using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
    done
  then show "dterm_sem (local.adjoint I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (local.adjoint I \<sigma> \<omega>) (Differential \<theta>)"
    by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow>  fsafe f'"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding TUadmit_def by auto
  then have sub1:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_dterm_adjoint'[OF dfree fsafe good_interp VA' dsafe] 
    by auto
qed

lemma uadmit_dterm_ntadjoint':
  assumes dfree:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Times \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Function x1a x2a)
    assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
      dsafe x \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) x = dterm_sem (adjointFO I \<sigma> \<omega>) x"
    assume safe:"dsafe (Function x1a x2a)"
    from safe have safes:"\<And>j. dsafe (x2a j)" by auto
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
      dterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2a j)"
      using rangeI safes by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. x1a = Inr a\<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
      using SIGT by auto
    have VAf:"\<And>a. x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a))"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "x1a")
     defer
     subgoal for x1 x2 a
     proof -
       assume VA:"(\<And>a. x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))"
       assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2a j) (x1,x2))"
       assume some:"x1a = Inr a"
       note FVT = VAf[OF some]
       have dsafe:"\<And>i. dsafe (\<sigma> i)"
         using dfree dfree_is_dsafe by auto
       have dsem:"\<And>R . dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
         using coincidence_dterm[OF dsafe FVT] by auto
       have "\<And>R. Functions (adjointFO I \<sigma> \<nu>) x1a R = Functions (adjointFO I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjointFO_def by auto
       then show "Functions (adjointFO I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                  Functions (adjointFO I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) (x1,x2))"
         by auto
     qed
    unfolding adjointFO_def apply auto    
    done
next
  case (Differential \<theta>)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Differential \<theta>)}. FVT (\<sigma> i))"
  assume safe:"dsafe (Differential \<theta>)"
  then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
  from VA have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    by auto
  have dsafe:"\<And>i. dsafe (\<sigma> i)"
    using dfree dfree_is_dsafe by auto
  have sem:"sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
    using uadmit_sterm_ntadjoint'[OF dsafe  VA'] by auto
  have good1:"is_interp (adjointFO I \<sigma> \<nu>)" using adjointFO_safe[OF good_interp dsafe, of "\<lambda>i. i"] by auto
  have good2:"is_interp (adjointFO I \<sigma> \<omega>)" using adjointFO_safe[OF good_interp dsafe, of "\<lambda>i. i"] by auto
  have frech:"frechet (adjointFO I \<sigma> \<nu>) \<theta> = frechet (adjointFO I \<sigma> \<omega>) \<theta>"
    apply (auto simp add: fun_eq_iff)
    subgoal for a b
      using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
    done
  then show "dterm_sem (adjointFO I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (adjointFO I \<sigma> \<omega>) (Differential \<theta>)"
    by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding NTUadmit_def by auto
  then have sub1:"(\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_dterm_ntadjoint'[OF dfree good_interp VA' dsafe] 
    by auto
qed

definition ssafe ::"('sf, 'sc, 'sz) subst \<Rightarrow> bool"
where "ssafe \<sigma> \<equiv>
  (\<forall> i f'. SFunctions \<sigma> i = Some f' \<longrightarrow> dfree f') \<and> 
  (\<forall> f f'. SPredicates \<sigma> f = Some f'  \<longrightarrow> fsafe f') \<and>
  (\<forall> f f'. SPrograms \<sigma> f = Some f'  \<longrightarrow> hpsafe f') \<and>
  (\<forall> f f'. SODEs \<sigma> f = Some f'  \<longrightarrow> osafe f') \<and>
  (\<forall> C C'. SContexts \<sigma> C = Some C'  \<longrightarrow> fsafe C')"

lemma uadmit_dterm_adjointS:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  fixes \<nu> \<omega>
  assumes VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  assumes dsafe:"dsafe \<theta>"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  show "?thesis" 
    apply(rule uadmit_dterm_adjoint')
    using good_interp ssafe VA dsafe unfolding ssafe_def by auto 
qed

lemma adj_sub_assign_fact:"\<And>i j e. i\<in>SIGT e \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT e}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
     by auto
  done

lemma adj_sub_geq1_fact:"\<And>i j x1 x2. i\<in>SIGT x1 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
     by auto
  done

lemma adj_sub_geq2_fact:"\<And>i j x1 x2. i\<in>SIGT x2 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
     by auto
  done
lemma adj_sub_prop_fact:"\<And>i j x1 x2 k. i\<in>SIGT (x2 k) \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         insert (Inr (Inr x1)) {Inl x |x. \<exists>xa. x \<in> SIGT (x2 xa)}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
     by auto
  done

lemma adj_sub_ode_fact:"\<And>i j x1 x2. Inl i \<in> SIGO x1 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         (SIGF x2 \<union> {Inl x |x. Inl x \<in> SIGO x1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO x1})"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
     by auto
  done

lemma adj_sub_assign:"\<And>e \<sigma> x. (\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
subgoal for e \<sigma> x
 unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> j")
     apply auto
    subgoal for a
      using adj_sub_assign_fact[of j e i]
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
    done
  done
done

lemma adj_sub_diff_assign:"\<And>e \<sigma> x. (\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
  subgoal for e \<sigma> x
    unfolding SDom_def apply auto
    subgoal for i j
      apply (cases "SFunctions \<sigma> j")
       apply auto
      subgoal for a
        using adj_sub_assign_fact[of j e i]
        by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
      done
    done
  done
   
lemma adj_sub_geq1:"\<And>\<sigma> x1 x2. (\<Union>i\<in>SIGT x1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2
    unfolding SDom_def apply auto
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
        using adj_sub_geq1_fact[of i x1 x \<sigma>] 
        by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
      done
    done
  done

lemma adj_sub_geq2:"\<And>\<sigma> x1 x2. (\<Union>i\<in>SIGT x2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2
    unfolding SDom_def apply auto
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
        using adj_sub_geq2_fact[of i x2 x \<sigma>] 
        by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
      done
    done
  done

lemma adj_sub_prop:"\<And>\<sigma> x1 x2 j . (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2 j
    unfolding SDom_def apply auto
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
        using adj_sub_prop_fact[of i x2 j x \<sigma> x1] 
        by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))     
      done
    done
  done

lemma adj_sub_ode:"\<And>\<sigma> x1 x2. (\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2
    unfolding SDom_def apply auto
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
        using adj_sub_ode_fact[of i x1 x \<sigma> x2]
        by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5)) 
     done
   done
  done

lemma uadmit_ode_adjoint':
  fixes \<sigma> I
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<Longrightarrow> osafe ODE \<Longrightarrow> ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
proof (induction ODE)
  case (OVar x)
  then show ?case unfolding adjoint_def by auto
next
  case (OSing x1a x2)
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OSing x1a x2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
    assume osafe:"osafe (OSing x1a x2)"
    then have dfree:"dfree x2" by (auto dest: osafe.cases)
    have safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      using ssafe unfolding ssafe_def using dfree_is_dsafe by auto
    have sem:"sterm_sem (local.adjoint I \<sigma> \<nu>) x2 = sterm_sem (local.adjoint I \<sigma> \<omega>) x2"
       using uadmit_sterm_adjoint'[of \<sigma> \<nu> \<omega> x2 I, OF safes, of "(\<lambda> x y. x)" "(\<lambda> x y. x)"] VA
       by auto
    show ?case 
      apply auto
      apply (rule ext)
      subgoal for x
        apply (rule vec_extensionality)
        using sem by auto
      done
next
  case (OProd ODE1 ODE2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<Longrightarrow>
      osafe ODE1 \<Longrightarrow> ODE_sem (local.adjoint I \<sigma> \<nu>) ODE1 = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE2}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<Longrightarrow>
    osafe ODE2 \<Longrightarrow> ODE_sem (local.adjoint I \<sigma> \<nu>) ODE2 = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
    assume safe:"osafe (OProd ODE1 ODE2)"
    from safe have safe1:"osafe ODE1" and safe2:"osafe ODE2" by (auto dest: osafe.cases) 
    have sub1:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<subseteq> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
      by auto
    have sub2:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE2}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<subseteq> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
qed

lemma uadmit_ode_ntadjoint':
  fixes \<sigma> I
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<Longrightarrow> osafe ODE \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE = ODE_sem (adjointFO I \<sigma> \<omega>) ODE"
proof (induction ODE)
  case (OVar x)
  then show ?case unfolding adjointFO_def by auto
next
  case (OSing x1a x2)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO (OSing x1a x2)}. FVT (\<sigma> y))"
  assume osafe:"osafe (OSing x1a x2)"
  then have dfree:"dfree x2" by (auto dest: osafe.cases)
  have sem:"sterm_sem (adjointFO I \<sigma> \<nu>) x2 = sterm_sem (adjointFO I \<sigma> \<omega>) x2"
     using uadmit_sterm_ntadjoint'[of \<sigma> \<nu> \<omega> x2 I, OF ssafe] VA
     by auto
  show ?case 
    apply auto
    apply (rule ext)
    subgoal for x
      apply (rule vec_extensionality)
      using sem by auto
    done
next
  case (OProd ODE1 ODE2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE1}. FVT (\<sigma> y)) \<Longrightarrow>
    osafe ODE1 \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE1 = ODE_sem (adjointFO I \<sigma> \<omega>) ODE1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE2}. FVT (\<sigma> y)) \<Longrightarrow>
    osafe ODE2 \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE2 = ODE_sem (adjointFO I \<sigma> \<omega>) ODE2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
  assume safe:"osafe (OProd ODE1 ODE2)"
  from safe have safe1:"osafe ODE1" and safe2:"osafe ODE2" by (auto dest: osafe.cases) 
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
qed

lemma adjoint_ode_vars:
  shows "ODE_vars (local.adjoint I \<sigma> \<nu>) ODE = ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
  apply(induction ODE)
  unfolding adjoint_def by auto

lemma uadmit_mkv_adjoint:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  assumes VA:"Vagree \<nu> \<omega> (\<Union>i \<in> {i | i. (Inl i\<in>SIGO ODE)}. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  assumes osafe:"osafe ODE"
  shows "mk_v (adjoint I \<sigma> \<nu>) ODE = mk_v (adjoint I \<sigma> \<omega>) ODE"
  apply(rule ext)
  subgoal for R
    apply(rule ext)
    subgoal for solt
      apply(rule agree_UNIV_eq)
      using mk_v_agree[of "(adjoint I \<sigma> \<nu>)" ODE "R" solt]
      using mk_v_agree[of "(adjoint I \<sigma> \<omega>)" ODE "R" solt]
      using uadmit_ode_adjoint'[OF ssafe good_interp VA osafe]
      unfolding Vagree_def
      apply auto
       subgoal for i
         apply (cases "Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE")
       proof -
         assume sem_eq:"ODE_sem (local.adjoint I \<sigma> \<nu>) ODE = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (local.adjoint I \<sigma> \<nu>) ODE = ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
           apply(induction ODE)
           unfolding adjoint_def by auto
         assume thing1:" 
           \<forall>i. (Inl i \<in> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow> fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i) \<and>
             (Inl i \<in> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow> fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i)"
         assume thing2:" 
           \<forall>i. (Inl i \<in> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow> fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i) \<and>
             (Inl i \<in> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow> fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i)"
         assume inl:"Inl i \<in> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
          from thing1 and inl have eq1: "fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i"
            using vars_eq by auto
          from thing2 and inl have eq2: "fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i"
            using vars_eq by auto
         show "fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       next
         assume sem_eq:"ODE_sem (local.adjoint I \<sigma> \<nu>) ODE = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. Inl i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<and> Inl i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
        fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst R $ i"
         assume thing2:"\<forall>i. Inl i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<and> Inl i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
        fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = fst R $ i"
         assume inl:"Inl i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (local.adjoint I \<sigma> \<nu>) ODE = ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
           apply(induction ODE)
             unfolding adjoint_def by auto
         from thing1 and inl have eq1: "fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst R $ i"
           using vars_eq by auto
         from thing2 and inl have eq2: "fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = fst R $ i"
           using vars_eq by auto
         show "fst (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       qed
      subgoal for i
        apply (cases "Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE")
       proof -
         assume sem_eq:"ODE_sem (local.adjoint I \<sigma> \<nu>) ODE = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. (Inr i \<in> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
             snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE solt $ i) \<and>
            (Inr i \<in> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
              snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE solt $ i)"
         assume thing2:"\<forall>i. (Inr i \<in> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
              snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE solt $ i) \<and>
             (Inr i \<in> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
          snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE solt $ i)"
         assume inr:"Inr i \<in> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (local.adjoint I \<sigma> \<nu>) ODE = ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
          apply(induction ODE)
            unfolding adjoint_def by auto
         show "snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using thing1 thing2 vars_eq inr by auto
       next
         assume sem_eq:"ODE_sem (local.adjoint I \<sigma> \<nu>) ODE = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. Inr i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<and> Inr i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
             snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd R $ i"
         assume thing2:"\<forall>i. Inr i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<and> Inr i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
             snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = snd R $ i"
         assume inr:"Inr i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (local.adjoint I \<sigma> \<nu>) ODE = ODE_vars (local.adjoint I \<sigma> \<omega>) ODE"
          apply(induction ODE)
            unfolding adjoint_def by auto
         have eq1:"snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd R $ i"
           using thing1 sem_eq vars_eq inr by auto
         have eq2:"snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i = snd R $ i"
           using thing2 sem_eq vars_eq inr by auto
         show "snd (mk_v (local.adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd (mk_v (local.adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       qed
      done
    done
  done

lemma adjointFO_ode_vars:
  shows "ODE_vars (adjointFO I \<sigma> \<nu>) ODE = ODE_vars (adjointFO I \<sigma> \<omega>) ODE"
  apply(induction ODE)
    unfolding adjointFO_def by auto

lemma uadmit_mkv_ntadjoint:
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  assumes VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y))"
  assumes osafe:"osafe ODE"
  shows "mk_v (adjointFO I \<sigma> \<nu>) ODE = mk_v (adjointFO I \<sigma> \<omega>) ODE"
  apply(rule ext)
  subgoal for R
    apply(rule ext)
    subgoal for solt
      apply(rule agree_UNIV_eq)
      using mk_v_agree[of "(adjointFO I \<sigma> \<nu>)" ODE "R" solt]
      using mk_v_agree[of "(adjointFO I \<sigma> \<omega>)" ODE "R" solt]
      using uadmit_ode_ntadjoint'[OF ssafe good_interp VA osafe]
      unfolding Vagree_def
      apply auto
      using adjointFO_ode_vars by metis+
    done
  done
    
lemma uadmit_prog_fml_adjoint':
  fixes \<sigma> I
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGP \<alpha>. SFV \<sigma> x) \<Longrightarrow> hpsafe \<alpha> \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) \<alpha> = prog_sem (adjoint I \<sigma> \<omega>) \<alpha>"
  and "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x) \<Longrightarrow> fsafe \<phi> \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
proof (induct "\<alpha>" and "\<phi>")
  case (Pvar x)
  then show ?case unfolding adjoint_def by auto
next
  case (Assign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
  assume safe:"hpsafe (x := e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
    using adj_sub_assign[of \<sigma> e x] by auto
  have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
  assume safe:"hpsafe (DiffAssign x e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
    using adj_sub_diff_assign[of \<sigma> e] by auto
  have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (Test x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
  assume hpsafe:"hpsafe (? x)"
  then have fsafe:"fsafe x" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
    by auto
  have "fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
    using IH[OF agree_sub[OF sub VA] fsafe] by auto
  then show ?case by auto
next
  case (EvolveODE x1 x2)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
  assume safe:"hpsafe (EvolveODE x1 x2)"
  then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    by auto
  then have VAF:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a)"
    using agree_sub[OF sub1 VA] by auto 
  note IH' = IH[OF VAF fsafe]
  have sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    using adj_sub_ode[of \<sigma> x1 x2] by auto
  moreover have IH2:"ODE_sem (local.adjoint I \<sigma> \<nu>) x1 = ODE_sem (local.adjoint I \<sigma> \<omega>) x1"
    apply (rule uadmit_ode_adjoint')
       subgoal by (rule ssafe)
      subgoal by (rule good_interp)
     subgoal using agree_sub[OF sub VA] by auto
    subgoal by (rule osafe)
    done
  have mkv:"mk_v (adjoint I \<sigma> \<nu>) x1 = mk_v (adjoint I \<sigma> \<omega>) x1"
    apply (rule uadmit_mkv_adjoint)
       using ssafe good_interp osafe agree_sub[OF sub VA] by auto
  show ?case 
    apply auto
     subgoal for aa ba bb sol t
       apply(rule exI[where x = sol])
       apply(rule conjI)
        subgoal by auto
       apply(rule exI[where x=t])
       apply(rule conjI)
        subgoal using mkv by auto
       apply(rule conjI)
        subgoal by auto using IH2 mkv IH' by auto
    subgoal for aa ba bb sol t
      apply(rule exI[where x = sol])
      apply(rule conjI)
       subgoal by auto
      apply(rule exI[where x=t])
      apply(rule conjI)
       subgoal using mkv by auto
      apply(rule conjI)
       subgoal by auto using IH2 mkv IH' by auto
    done
next
  case (Choice x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
  assume safe:"hpsafe (x1 \<union>\<union> x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
    by auto
  have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Sequence x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
  assume safe:"hpsafe (x1 ;; x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
    by auto
  have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Loop x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x = prog_sem (local.adjoint I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x**). SFV \<sigma> a)"
  assume safe:"hpsafe (x**)"
  from safe have
    safe:"hpsafe x"
    by (auto dest: hpsafe.cases)
  have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x**). SFV \<sigma> a)"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (Geq x1 x2)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (Geq x1 x2)"
  then have dsafe1:"dsafe x1" and dsafe2:"dsafe x2" by (auto dest: fsafe.cases)
  have sub1:"(\<Union>i\<in>SIGT x1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    using adj_sub_geq1[of \<sigma> x1 x2] by auto
  have sub2:"(\<Union>i\<in>SIGT x2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    using adj_sub_geq2[of \<sigma> x2 x1] by auto
  have "dterm_sem (local.adjoint I \<sigma> \<nu>) x1 = dterm_sem (local.adjoint I \<sigma> \<omega>) x1"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
  moreover have "dterm_sem (local.adjoint I \<sigma> \<nu>) x2 = dterm_sem (local.adjoint I \<sigma> \<omega>) x2"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
  ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe ($\<phi> x1 x2)"
  then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
  have subs:"\<And>j. (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
    subgoal for j using adj_sub_prop[of \<sigma> x2 j x1] by auto
    done
  have "\<And>i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i)"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF subs VA] safes])
  then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i) R)"
    by (auto simp add: vec_eq_iff)
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    unfolding Vagree_def SIGT.simps using rangeI 
    by (metis (no_types, lifting) subsetD subs)
  have SIGF:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Inr (Inr x1) \<in> SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2)" unfolding SDom_def
    by auto
  have VAsub:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> (FVF a) \<subseteq> (\<Union>i\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> i)"
    using SIGF by auto
  have VAf:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVF a)"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    apply(cases "SPredicates \<sigma> x1")
    defer
    subgoal for a
    proof -
      assume some:"SPredicates \<sigma> x1 = Some a"
      note FVF = VAf[OF some]
      have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
        using ssafe dfree_is_dsafe unfolding ssafe_def by auto
      have dsem:"\<And>R . (\<nu> \<in> fml_sem (extendf I R) a) = (\<omega> \<in> fml_sem (extendf I R) a)"
        subgoal for R
          apply (rule coincidence_formula)
            subgoal using ssafe unfolding ssafe_def using some by auto
           subgoal unfolding Iagree_def by auto
          subgoal by (rule FVF)
        done
      done
      have pred_eq:"\<And>R. Predicates (local.adjoint I \<sigma> \<nu>) x1 R = Predicates (local.adjoint I \<sigma> \<omega>) x1 R"
        using dsem some unfolding adjoint_def by auto
      show "fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> x1 x2) = fml_sem (local.adjoint I \<sigma> \<omega>) ($\<phi> x1 x2)"
        apply auto
         subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
        subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
        done
    qed
    unfolding adjoint_def using local.adjoint_def local.vec_eq apply auto
    done
next
  case (Not x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x = fml_sem (local.adjoint I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
  assume safe:"fsafe (Not x)"
  from safe have
    safe:"fsafe x"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (And x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x1 = fml_sem (local.adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (And x1 x2)"
  from safe have
    safe1:"fsafe x1"
    and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
    by auto
  have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Exists x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (Exists x1 x2)"
  from safe have safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (Diamond x1 x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
    by auto
  have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (InContext x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (InContext x1 x2)"
  from safe have  safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
    by auto
  show ?case using IH1[OF agree_sub[OF sub VA] safe1]  
    unfolding adjoint_def by auto
qed
 
lemma uadmit_prog_adjoint:
  assumes PUA:"PUadmit \<sigma> a U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes hpsafe:"hpsafe a"
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "prog_sem (adjoint I \<sigma> \<nu>) a = prog_sem (adjoint I \<sigma> \<omega>) a"
proof -
  have sub:"(\<Union>x\<in>SDom \<sigma> \<inter> SIGP a. SFV \<sigma> x) \<subseteq> -U" using PUA unfolding PUadmit_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGP a. SFV \<sigma> x)" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_adjoint'[OF ssafe good_interp])
     subgoal by (rule VA')
    subgoal by (rule hpsafe)
    done
qed

lemma uadmit_fml_adjoint:
  assumes FUA:"FUadmit \<sigma> \<phi> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
proof -
  have sub:"(\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x) \<subseteq> -U" using FUA unfolding FUadmit_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x)" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_adjoint'[OF ssafe good_interp])
     subgoal by (rule VA')
    subgoal by (rule fsafe)
    done
qed

lemma ntadj_sub_assign:"\<And>e \<sigma> x. (\<Union>y\<in>{y. Inr y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_diff_assign:"\<And>e \<sigma> x. (\<Union>y\<in>{y. Inl y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
  by auto
   
lemma ntadj_sub_geq1:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. Inl y \<in> SIGT x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_geq2:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. Inl y \<in> SIGT x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_prop:"\<And>\<sigma> x1 x2 j. (\<Union>y\<in>{y. Inl y \<in> SIGT (x2 j)}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGF ($\<phi> x1 x2)}.FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_ode:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGO x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inl y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma uadmit_prog_fml_ntadjoint':
  fixes \<sigma> I
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inr x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<Longrightarrow> hpsafe \<alpha> \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) \<alpha> = prog_sem (adjointFO I \<sigma> \<omega>) \<alpha>"
  and "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inr x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<Longrightarrow> fsafe \<phi> \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
proof (induct "\<alpha>" and "\<phi>")
  case (Pvar x)
  then show ?case unfolding adjointFO_def by auto
next
  case (Assign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x := e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inr y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
    using ntadj_sub_assign[of \<sigma> e x] by auto
  have VA':"(Vagree \<nu> \<omega> (\<Union>i\<in>{i. Inr i \<in> SIGT e}. FVT (\<sigma> i)))"
    using agree_sub[OF sub VA] by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) e = dterm_sem (adjointFO I \<sigma> \<omega>) e"
    using uadmit_dterm_ntadjoint'[of \<sigma> I \<nu> \<omega> e] ssafe good_interp agree_sub[OF sub VA] dsafe by auto
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (DiffAssign x e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inr y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
    using ntadj_sub_assign[of \<sigma> e x] by auto
  have VA':"(Vagree \<nu> \<omega> (\<Union>i\<in>{i. Inr i \<in> SIGT e}. FVT (\<sigma> i)))"
    using agree_sub[OF sub VA] by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) e = dterm_sem (adjointFO I \<sigma> \<omega>) e"
    using uadmit_dterm_ntadjoint'[of \<sigma> I \<nu> \<omega> e] ssafe good_interp agree_sub[OF sub VA] dsafe by auto
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (Test x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (? x)}. FVT (\<sigma> y))"
  assume hpsafe:"hpsafe (? x)"
  then have fsafe:"fsafe x" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (? x)}. FVT (\<sigma> y))"
    by auto
  have "fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
    using IH[OF agree_sub[OF sub VA] fsafe] by auto
  then show ?case by auto
next
  case (EvolveODE x1 x2)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (EvolveODE x1 x2)"
  then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
    by auto
  then have VAF:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y))"
    using agree_sub[OF sub1 VA] by auto 
  note IH' = IH[OF VAF fsafe]
  have sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
    by auto
  moreover have IH2:"ODE_sem (adjointFO I \<sigma> \<nu>) x1 = ODE_sem (adjointFO I \<sigma> \<omega>) x1"
    apply (rule uadmit_ode_ntadjoint')
       subgoal by (rule ssafe)
      subgoal by (rule good_interp)
     defer subgoal by (rule osafe)
    using agree_sub[OF sub VA] by auto
  have mkv:"mk_v (adjointFO I \<sigma> \<nu>) x1 = mk_v (adjointFO I \<sigma> \<omega>) x1"
    apply (rule uadmit_mkv_ntadjoint)
       using ssafe good_interp osafe agree_sub[OF sub VA] by auto
  show ?case 
    apply auto
    subgoal for aa ba bb sol t
      apply(rule exI[where x = sol])
      apply(rule conjI)
       subgoal by auto
      apply(rule exI[where x=t])
      apply(rule conjI)
       subgoal using mkv by auto
      apply(rule conjI)
       subgoal by auto using IH2 mkv IH' by auto
    subgoal for aa ba bb sol t
      apply(rule exI[where x = sol])
      apply(rule conjI)
       subgoal by auto
      apply(rule exI[where x=t])
      apply(rule conjI)
       subgoal using mkv by auto
      apply(rule conjI)
       subgoal by auto using IH2 mkv IH' by auto
    done
next
  case (Choice x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x2}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x2 = prog_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x1 \<union>\<union> x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1)}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x2)}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Sequence x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x2}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x2 = prog_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x1 ;; x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Loop x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x = prog_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x** )}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x** )"
  from safe have
    safe:"hpsafe x"
    by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x )}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP (x** )}. FVT (\<sigma> y))"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (Geq x1 x2)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Geq x1 x2)"
  then have dsafe1:"dsafe x1" and dsafe2:"dsafe x2" by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inr y \<in> SIGT x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inr y \<in> SIGT x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
    by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) x1 = dterm_sem (adjointFO I \<sigma> \<omega>) x1"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
  moreover have "dterm_sem (adjointFO I \<sigma> \<nu>) x2 = dterm_sem (adjointFO I \<sigma> \<omega>) x2"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
  ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF ($\<phi> x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe ($\<phi> x1 x2)"
  then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
  have subs:"\<And>j. (\<Union>y\<in>{y. Inr y \<in> SIGT (x2 j)}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF ($\<phi> x1 x2)}. FVT (\<sigma> y))"
    subgoal for j  by auto
    done
  have "\<And>i. dterm_sem (adjointFO I \<sigma> \<nu>) (x2 i) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2 i)"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF subs VA] safes])
  then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2 i) R)"
    by (auto simp add: vec_eq_iff)
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inr y \<in> SIGT (x2 j)}. FVT (\<sigma> y))"
    subgoal for j 
      using agree_sub[OF subs[of j] VA] by auto
    done
  then show ?case 
    using vec_eq by (auto simp add: adjointFO_def)
next
  case (Not x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Not x)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Not x)"
  from safe have
    safe:"fsafe x"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Not x)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (And x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x1}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x1 = fml_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (And x1 x2)"
  from safe have
    safe1:"fsafe x1"
and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x1}. FVT (\<sigma> y))  \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y))  \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Exists x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Exists x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Exists x1 x2)"
  from safe have safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Exists x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Diamond x1 x2)"
  from safe have
    safe1:"hpsafe x1"
and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGP x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (InContext x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (InContext x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (InContext x1 x2)"
  from safe have  safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGF (InContext x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub VA] safe1]  
    unfolding adjointFO_def by auto
qed

lemma uadmit_prog_ntadjoint:
  assumes TUA:"PUadmitFO \<sigma> \<alpha> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes good_interp:"is_interp I"
  shows  "prog_sem (adjointFO I \<sigma> \<nu>) \<alpha> = prog_sem (adjointFO I \<sigma> \<omega>) \<alpha>"
proof -
  have sub:"(\<Union>x\<in>{x. Inl (Inr x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding PUadmitFO_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inr x) \<in> SIGP \<alpha>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
     subgoal by (rule VA')
    subgoal by (rule hpsafe)
    done
qed

lemma uadmit_fml_ntadjoint:
  assumes TUA:"FUadmitFO \<sigma> \<phi> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes fsafe:"fsafe \<phi>"
  assumes good_interp:"is_interp I"
  shows  "fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
proof -
  have sub:"(\<Union>x\<in>{x. Inl (Inr x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding FUadmitFO_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inr x) \<in> SIGF \<phi>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
     subgoal by (rule VA')
    subgoal by (rule fsafe)
    done
qed

subsection\<open>Substitution theorems for terms\<close>
lemma nsubst_sterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  shows "TadmitFFO \<sigma> \<theta>  \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> sterm_sem I (TsubstFO \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: TadmitFFO.induct)
  case (TadmitFFO_Fun1 \<sigma> args f)
  then show ?case by(auto simp add:  adjointFO_def)
next
  case (TadmitFFO_Fun2 \<sigma> args f)
  then show ?case
    apply(auto simp add: adjointFO_def) 
    by (simp add: dsem_to_ssem)
qed (auto)

lemma nsubst_sterm':
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes a b::"'sz simple_state"
  shows "TadmitFFO \<sigma> \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> sterm_sem I (TsubstFO \<theta> \<sigma>) a = sterm_sem (adjointFO I \<sigma> (a,b)) \<theta> a"
  using nsubst_sterm by (metis fst_conv)

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(TsubstFO \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dfree.intros)
qed (auto intro: dfree.intros)

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case" 
    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)
qed (auto intro: dfree.intros)

lemma subst_sterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  shows "
    TadmitF \<sigma> \<theta>  \<Longrightarrow>
    (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
     sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: TadmitF.induct)
  case (TadmitF_Fun1  \<sigma> args f f') then
    have subFree:" TadmitFFO (\<lambda>i. Tsubst (args i) \<sigma>) f'" 
      and frees:"\<And>i. dfree (Tsubst (args i) \<sigma>)" 
      and TFA:"\<And>i. TadmitF \<sigma> (args i)"
      and NTFA:"TadmitFFO (\<lambda>i. Tsubst (args i) \<sigma>) f'"
      and theIH:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (local.adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
        by auto
      from frees have safes:"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
        by (simp add: dfree_is_dsafe) 
  assume subFreeer:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
  note admit = TadmitF_Fun1.hyps(1) and sfree = TadmitF_Fun1.prems(1)
  have IH:"(\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
    using  admit TadmitF_Fun1.prems TadmitF_Fun1.IH by auto
  have vec_eq:"(\<chi> i. sterm_sem (local.adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)) = (\<chi> i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>))"
    apply(rule vec_extensionality)
    using IH by auto
  assume some:"SFunctions \<sigma> f = Some f'" 
  let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
  have IH2:"sterm_sem I (TsubstFO f' ?sub) (fst \<nu>) = sterm_sem (adjointFO I ?sub \<nu>) f' (fst \<nu>)"
    apply(rule nsubst_sterm)
     apply(rule subFree)
    by (rule safes)
  show "?case"
    apply (simp add: some)
    unfolding vec_eq IH2
    by (auto simp add: some adjoint_free[OF subFreeer, of \<sigma> "(\<lambda> x y. x)" I \<nu>] adjointFO_free[OF frees])      
next
  case (TadmitF_Fun2  \<sigma> args f) 
  assume none:"SFunctions \<sigma> f = None" 
  note admit = TadmitF_Fun2.hyps(1) and sfree = TadmitF_Fun2.prems(1)
  have IH:"(\<And>i. TadmitF \<sigma> (args i) \<Longrightarrow>
      sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
    using  TadmitF_Fun2.prems TadmitF_Fun2.IH by auto
  have eqs:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
    by (auto simp add: IH admit)
  show "?case" 
    by(auto simp add: none IH adjoint_def vec_extensionality eqs)
  qed auto

lemma nsubst_dterm':
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  assumes good_interp:"is_interp I"    
  shows "TadmitFO \<sigma> \<theta> \<Longrightarrow> dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: TadmitFO.induct)
  case (TadmitFO_Fun \<sigma> args f)
  assume admit:"\<And>i. TadmitFO \<sigma> (args i)"
  assume IH:"\<And>i. dfree (args i) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>"
  assume free:"dfree ($f f args)"
  assume safe:"\<And>i. dsafe (\<sigma> i)"
  from free have frees: "\<And>i. dfree (args i)" by (auto dest: dfree.cases)
  have sem:"\<And>i. dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>"
    using IH[OF frees safe] by auto
  have vecEq:" (\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>) =
   (\<chi> i. dterm_sem
          \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. dterm_sem I (\<sigma> f') \<nu>), Predicates = Predicates I, Contexts = Contexts I,
             Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          (args i) \<nu>) "
    apply(rule vec_extensionality)
    by (auto simp add: adjointFO_def)
  show " dterm_sem I (TsubstFO ($f f args) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) ($f f args) \<nu>"
    apply (cases "f") 
     apply (auto simp add: vec_extensionality  adjointFO_def)
    using sem apply auto
    subgoal for a using vecEq by auto
    done
next
  case (TadmitFO_Diff \<sigma> \<theta>) 
  hence admit:"TadmitFFO \<sigma> \<theta>"
    and admitU:"NTUadmit \<sigma> \<theta> UNIV"
    (*and IH : "dfree \<theta> \<Longrightarrow>
          (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"*)
    and safe: "dfree (Differential \<theta>)" 
    and freeSub:"\<And>i. dsafe (\<sigma> i)"
    by auto
  from safe have "False" by (auto dest: dfree.cases)
  then show "dterm_sem I (TsubstFO (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
    by auto
qed (auto simp add: TadmitFO.cases)

lemma ntsubst_free_to_safe:
  "dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dsafe (TsubstFO \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto intro: dsafe.intros)

lemma ntsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dsafe (TsubstFO \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free dfree_is_dsafe)
next
  case (dsafe_Diff \<theta>) then show "?case"
    by  (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto simp add: ntsubst_preserves_free intro: dsafe.intros)

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) 
  assume dsafes:"\<And>i. dsafe (args i)"
  assume IH:"\<And>j. (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe (Tsubst (args j) \<sigma>)"
  assume frees:"\<And>i f. SFunctions \<sigma> i = Some f \<Longrightarrow> dfree f"
  have IH':"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
    using frees IH by auto
  then show "?case" 
    apply auto
    apply(cases "SFunctions \<sigma> i")
     subgoal using IH frees by auto
    subgoal for a using frees[of i a] ntsubst_free_to_safe[of a] IH' by auto
    done 
qed (auto intro: dsafe.intros tsubst_preserves_free)

lemma subst_dterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"
  shows "
    Tadmit \<sigma> \<theta> \<Longrightarrow>
    dsafe \<theta> \<Longrightarrow>
    (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
    (\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f') \<Longrightarrow>
    (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
proof (induction rule: Tadmit.induct)
  case (Tadmit_Fun1 \<sigma> args f f' \<nu>) 
  note safe = Tadmit_Fun1.prems(1) and sfree = Tadmit_Fun1.prems(2) and TA = Tadmit_Fun1.hyps(1)
    and some = Tadmit_Fun1.hyps(2) and NTA = Tadmit_Fun1.hyps(3)
  hence safes:"\<And>i. dsafe (args i)" by auto
  have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
      dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
    using  Tadmit_Fun1.prems Tadmit_Fun1.IH by auto
  have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
    by (auto simp add: IH safes)
  let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
  have subSafe:"(\<And>i. dsafe (?sub i))"
    using tsubst_preserves_safe[OF safes sfree]
    by (simp add: safes sfree tsubst_preserves_safe)
  have freef:"dfree f'" using sfree some by auto 
  have IH2:"dterm_sem I (TsubstFO f' ?sub) \<nu> = dterm_sem (adjointFO I ?sub \<nu>) f' \<nu>"
    by (simp add: nsubst_dterm'[OF good_interp NTA freef subSafe])
  have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
    apply(auto simp add: vec_eq_iff)
    subgoal for i
      using IH[of i, OF safes[of i]] 
      by auto
    done
  show "?case" 
    using IH safes eqs apply (auto simp add:  IH2  some good_interp)
    using some unfolding adjoint_def adjointFO_def by auto
next
  case (Tadmit_Fun2 \<sigma> args f \<nu>) 
  note safe = Tadmit_Fun2.prems(1) and sfree = Tadmit_Fun2.prems(2) and TA = Tadmit_Fun2.hyps(1)
  and none = Tadmit_Fun2.hyps(2) 
  hence safes:"\<And>i. dsafe (args i)" by auto
  have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
      dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
  using  Tadmit_Fun2.prems Tadmit_Fun2.IH by auto
  have Ieq:"Functions I f = Functions (adjoint I \<sigma> \<nu>) f"
    using none unfolding adjoint_def by auto
  have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
    apply(auto simp add: vec_eq_iff)
    subgoal for i using IH[of i, OF safes[of i]] by auto
    done
  show "?case" using none IH Ieq vec by auto
next
  case (Tadmit_Diff \<sigma> \<theta>)  then
  have TA:"Tadmit \<sigma> \<theta>"
    and TUA:"TUadmit \<sigma> \<theta> UNIV"
    and IH:"dsafe \<theta> \<Longrightarrow> (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
    and safe:"dsafe (Differential \<theta>)"
    and sfree:"\<And>i f'1. SFunctions \<sigma> i = Some f'1 \<Longrightarrow> dfree f'1"
    and spsafe:"\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f'"
      by auto
  from sfree have sdsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
    using dfree_is_dsafe by auto  
  have VA:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
  from safe have free:"dfree \<theta>" by (auto dest: dsafe.cases intro: dfree.intros)
  from free have tsafe:"dsafe \<theta>" using dfree_is_dsafe by auto
  have freeSubst:"dfree (Tsubst \<theta> \<sigma>)" 
    using tsubst_preserves_free[OF free sfree]
    using Tadmit_Diff.prems(2) free tsubst_preserves_free by blast 
  have IH':"\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>"
    using IH[OF tsafe sfree] by auto
  have sem_eq:"\<And>\<nu>'. dsafe \<theta> \<Longrightarrow> is_interp I \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (local.adjoint I \<sigma> \<nu>') \<theta>"
    subgoal for \<nu>'
      using uadmit_dterm_adjoint[OF TUA VA sfree spsafe, of "(\<lambda> x y. x)" "(\<lambda> x y. x)" I \<nu> \<nu>']
      by auto
    done
  have IH'':"\<And>\<nu>'. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu>' = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>'"
    subgoal for \<nu>'
      using sem_eq[OF tsafe good_interp, of \<nu>'] IH'[of \<nu>'] by auto
    done
  have sem_eq:"sterm_sem I (Tsubst \<theta> \<sigma>) = sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>" 
    apply (auto simp add: fun_eq_iff)
    subgoal for \<nu>'
      apply (cases "\<nu>'")
      subgoal for \<nu>''
        apply auto
        using dsem_to_ssem[OF free, of "(local.adjoint I \<sigma> \<nu>)" "(\<nu>',\<nu>')"] dsem_to_ssem[OF freeSubst, of I "(\<nu>',\<nu>')"] IH'[of "(\<nu>)"]
        apply auto
        using IH'' by auto
      done
    done
  show "?case"
    apply (auto simp add: directional_derivative_def fun_eq_iff)
    using sterm_determines_frechet[OF 
        good_interp 
        adjoint_safe[OF good_interp sfree] 
        tsubst_preserves_free[OF free sfree] 
        free sem_eq]
    by auto
qed auto  

subsection\<open>Substitution theorems for ODEs\<close>
lemma osubst_preserves_safe:
  assumes ssafe:"ssafe \<sigma>"
  shows "(osafe ODE \<Longrightarrow> Oadmit \<sigma> ODE U \<Longrightarrow> osafe (Osubst ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case using ssafe unfolding ssafe_def by (cases "SODEs \<sigma> c", auto intro: osafe.intros)
next
  case (osafe_Sing \<theta> x)
  then show ?case 
    using tsubst_preserves_free ssafe unfolding ssafe_def by (auto intro: osafe.intros)
next
  case (osafe_Prod ODE1 ODE2)
  moreover have "Oadmit \<sigma> ODE1 U" "Oadmit \<sigma> ODE2 U" "ODE_dom (Osubst ODE1 \<sigma>) \<inter>  ODE_dom (Osubst ODE2 \<sigma>) = {}"
    using osafe_Prod.prems by (auto dest: Oadmit.cases) 
  ultimately show ?case by (auto intro: osafe.intros)
qed

lemma nosubst_preserves_safe:
  assumes sfree:"\<And>i. dfree (\<sigma> i)"
  fixes \<alpha> ::"('a + 'd, 'b, 'c) hp" and \<phi> ::"('a + 'd, 'b, 'c) formula"
  shows "(osafe ODE \<Longrightarrow> OUadmitFO \<sigma> ODE U \<Longrightarrow> osafe (OsubstFO ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case by (auto intro: osafe.intros)
next
  case (osafe_Sing \<theta> x)
  then show ?case using sfree ntsubst_preserves_free[of \<theta> \<sigma>] unfolding OUadmitFO_def by (auto intro: osafe.intros)
next
  case (osafe_Prod ODE1 ODE2)
  assume safe1:"osafe ODE1"
    and safe2:"osafe ODE2"
    and disj:"ODE_dom ODE1 \<inter> ODE_dom ODE2 = {}"
    and IH1:"OUadmitFO \<sigma> ODE1 U \<Longrightarrow> osafe (OsubstFO ODE1 \<sigma>)"
    and IH2:"OUadmitFO \<sigma> ODE2 U \<Longrightarrow> osafe (OsubstFO ODE2 \<sigma>)"
    and NOUA:"OUadmitFO \<sigma> (OProd ODE1 ODE2) U"    
  have nosubst_preserves_ODE_dom:"\<And>ODE. ODE_dom (OsubstFO ODE \<sigma>) = ODE_dom ODE"
    subgoal for ODE
      apply(induction "ODE")
        by auto
    done
  have disj':"ODE_dom (OsubstFO ODE1 \<sigma>) \<inter> ODE_dom (OsubstFO ODE2 \<sigma>) = {}"
    using disj nosubst_preserves_ODE_dom by auto
  from NOUA have NOUA1:"OUadmitFO \<sigma> ODE1 U" and NOUA2:"OUadmitFO \<sigma>  ODE2 U"  unfolding OUadmitFO_def by auto
  then show ?case using IH1[OF NOUA1] IH2[OF NOUA2] disj' by (auto intro: osafe.intros)
qed

lemma nsubst_dterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  fixes \<nu>'::"'sz state"
  assumes good_interp:"is_interp I"    
  shows "TadmitFO \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: TadmitFO.induct)
  case (TadmitFO_Diff \<sigma> \<theta>) then
  have subFree:"(\<And>i. dsafe (\<sigma> i))"
    and  NTFA:"TadmitFFO \<sigma> \<theta>"
    and substFree:"dfree (TsubstFO \<theta> \<sigma>)"
    and dsafe:"dsafe (Differential \<theta>)"
    and subSafe:"\<And>i. dsafe (\<sigma> i)"
    and  NTU:"NTUadmit \<sigma> \<theta> UNIV"  
    by auto   
  have dfree:"dfree \<theta>" using dsafe by auto
  then show ?case
    apply auto
    apply (unfold directional_derivative_def) 
    apply (rule sterm_determines_frechet)
    subgoal using good_interp by auto
       subgoal using adjointFO_safe[OF good_interp, of \<sigma>] subSafe by auto
      subgoal  using substFree by auto
     subgoal using dfree by auto
    subgoal
      apply(rule ext)
      subgoal for x
        using nsubst_sterm'[of  \<sigma> \<theta> I "(fst \<nu>)" "(snd \<nu>)", OF NTFA subSafe] apply auto
      proof -
        assume sem:"sterm_sem I (TsubstFO \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> (fst \<nu>)"
        have VA:"\<And>\<nu> \<omega>. Vagree \<nu> (x,snd \<nu>) (-UNIV)" unfolding Vagree_def by auto
        show "sterm_sem I (TsubstFO \<theta> \<sigma>) x = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> x"
          using uadmit_sterm_ntadjoint[OF NTU VA subSafe, OF  good_interp, of "(x, snd \<nu>)"]
            nsubst_sterm[OF NTFA subSafe, of I \<nu> ] 
          apply auto
          using NTU VA dfree_is_dsafe  dsafe subSafe substFree good_interp uadmit_sterm_ntadjoint
          by (metis NTFA fst_eqD nsubst_sterm)
      qed
    done
  done
next
  case (TadmitFO_Fun \<sigma> args f)
  then show ?case apply auto apply(cases f) unfolding adjointFO_def by auto
qed (auto)
  
lemma nsubst_ode:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  fixes \<nu>'::"'sz state"
  assumes good_interp:"is_interp I"    
  shows "osafe ODE \<Longrightarrow> OadmitFO \<sigma> ODE U \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (fst \<nu>)= ODE_sem (adjointFO I \<sigma> \<nu>) ODE (fst \<nu>)"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case unfolding OUadmitFO_def adjointFO_def by auto
next
  case (osafe_Sing \<theta> x)
  then show ?case apply auto
    using nsubst_sterm' [of  \<sigma> \<theta> I "(fst \<nu>)" "(snd \<nu>)"] by auto
next
  case (osafe_Prod ODE1 ODE2) then
  have NO1:"OadmitFO \<sigma> ODE1 U" and NO2:"OadmitFO \<sigma> ODE2 U" 
    unfolding OUadmitFO_def by auto
  have "ODE_sem I (OsubstFO ODE1 \<sigma>) (fst \<nu>) = ODE_sem (adjointFO I \<sigma> \<nu>) ODE1 (fst \<nu>)"
    "ODE_sem I (OsubstFO ODE2 \<sigma>) (fst \<nu>) = ODE_sem (adjointFO I \<sigma> \<nu>) ODE2 (fst \<nu>)" using osafe_Prod.IH osafe_Prod.prems osafe_Prod.hyps
    using NO1 NO2 by auto
  then show ?case by auto
qed
    
lemma osubst_preserves_BVO:
  shows "BVO (OsubstFO ODE \<sigma>) = BVO ODE"
proof (induction "ODE")
qed (auto)

lemma osubst_preserves_ODE_vars:
  shows "ODE_vars I (OsubstFO ODE \<sigma>) = ODE_vars (adjointFO I \<sigma> \<nu>) ODE"
proof (induction "ODE")
qed (auto simp add: adjointFO_def)

lemma osubst_preserves_semBV:
  shows "semBV I (OsubstFO ODE \<sigma>) = semBV (adjointFO I \<sigma> \<nu>) ODE"
proof (induction "ODE")
qed (auto simp add: adjointFO_def)

lemma nsubst_mkv:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  fixes \<nu>'::"'sz state"
  assumes good_interp:"is_interp I"  
  assumes NOU:"OadmitFO \<sigma> ODE U"
  assumes osafe:"osafe ODE "
  assumes frees:"(\<And>i. dsafe (\<sigma> i))"
  shows "(mk_v I (OsubstFO ODE \<sigma>) \<nu> (fst \<nu>')) 
    = (mk_v (adjointFO I \<sigma> \<nu>') ODE \<nu> (fst \<nu>'))"
  apply(rule agree_UNIV_eq)
  using mk_v_agree[of "adjointFO I \<sigma> \<nu>'" "ODE" \<nu> "fst \<nu>'"]
  using mk_v_agree[of "I" "OsubstFO ODE \<sigma>" \<nu> "fst \<nu>'"] 
  unfolding Vagree_def 
  using nsubst_ode[OF good_interp osafe NOU frees, of \<nu>']
  apply auto
   subgoal for i
     apply(erule allE[where x=i])+
     apply(cases "Inl i \<in> semBV I (OsubstFO ODE \<sigma>)")
      using  osubst_preserves_ODE_vars
      by (metis (full_types))+
  subgoal for i
    apply(erule allE[where x=i])+
    apply(cases "Inr i \<in> BVO ODE")
     using  osubst_preserves_ODE_vars
     by (metis (full_types))+
  done

lemma ODE_unbound_zero:
  fixes i
  shows "Inl i \<notin> BVO ODE \<Longrightarrow> ODE_sem I ODE x $ i = 0"
proof (induction ODE)
qed (auto)

lemma ODE_bound_effect:
  fixes s t sol ODE X b
  assumes s:"s \<in> {0..t}"
  assumes sol:"(sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t}  X"
  shows "Vagree (sol 0,b) (sol s, b) (-(BVO ODE))"
proof -
  have "\<And>i. Inl i \<notin> BVO ODE \<Longrightarrow>  (\<forall> s. s \<in> {0..t} \<longrightarrow> sol s $ i = sol 0 $ i)"
    apply auto
    apply (rule constant_when_zero)
         using s sol apply auto
    using ODE_unbound_zero solves_ode_subset 
    by fastforce+
  then show "Vagree (sol 0, b) (sol s, b) (- BVO ODE)"
    unfolding Vagree_def 
    using s  by (metis Compl_iff fst_conv  snd_conv)
qed

lemma NO_sub:"OadmitFO \<sigma> ODE A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> OadmitFO \<sigma> ODE B"
  by(induction ODE, auto simp add: OUadmitFO_def)

lemma NO_to_NOU:"OadmitFO \<sigma> ODE S \<Longrightarrow> OUadmitFO \<sigma> ODE S"
  by(induction ODE, auto simp add: OUadmitFO_def)
  
subsection\<open>Substitution theorems for formulas and programs\<close>
lemma nsubst_hp_fml:
  fixes I::"('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"    
  shows " (NPadmit \<sigma> \<alpha> \<longrightarrow> (hpsafe \<alpha> \<longrightarrow> (\<forall>i. dsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) \<alpha>)))) \<and>
    (NFadmit \<sigma> \<phi> \<longrightarrow> (fsafe \<phi> \<longrightarrow> (\<forall>i. dsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))))"
proof (induction rule: NPadmit_NFadmit.induct)
  case (NPadmit_Pvar \<sigma> a)
  then show ?case unfolding adjointFO_def by auto
next
  case (NPadmit_ODE \<sigma> ODE \<phi>) then
  have  NOU:"OadmitFO \<sigma> ODE (BVO ODE)"
    and NFA:"NFadmit \<sigma> \<phi>"
    and NFU:"FUadmitFO \<sigma> \<phi> (BVO ODE)"
    and fsafe:"fsafe (FsubstFO \<phi> \<sigma>)"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and osafe':"osafe (OsubstFO ODE \<sigma>)"
      by auto
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>  (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (EvolveODE ODE \<phi>)))"
  proof -
    assume safe:"hpsafe (EvolveODE ODE \<phi>)"
    then have osafe:"osafe ODE" and fsafe:"fsafe \<phi>" by auto
    assume frees:"(\<And>i. dsafe (\<sigma> i))"
    fix \<nu> \<omega>
    show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (EvolveODE ODE \<phi>))"
    proof (auto)
      fix b 
        and sol :: "real \<Rightarrow>(real, 'sz) vec" 
        and t :: real
      assume eq1:"\<nu> = (sol 0, b)"
      assume eq2:"\<omega> = mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)"
      assume t:"0 \<le> t"
      assume sol:"(sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t} 
         {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
      have agree_sem:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>)))"
        subgoal for t
          using mk_v_agree[of I "OsubstFO ODE \<sigma>" "(sol 0, b)" "sol t"] unfolding Vagree_def apply auto
          done
        done
      have bv_sub:"(-BVO ODE) \<subseteq> - (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>))"
        by(induction ODE, auto) 
      have agree:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- BVO ODE)"
        using agree_sub[OF bv_sub agree_sem] by auto
      \<comment> \<open>Necessary\<close>
      have mkv:"\<And>t. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol t, b)) ODE (sol 0, b) (sol t)"
        using nsubst_mkv[OF good_interp NOU osafe frees]
        by auto
      have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (-(BVO ODE))"
        using ODE_bound_effect sol
        by (metis osubst_preserves_BVO)
      have FVT_sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<subseteq> (-(BVO ODE))"
        using NOU NO_to_NOU OUadmitFO_def 
        by fastforce
      have agrees:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y))" 
        subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
      have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE  = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE"
        subgoal for s
          apply (rule uadmit_mkv_ntadjoint)
             prefer 3
             using NOU hmm[of s] NO_to_NOU unfolding OUadmitFO_def Vagree_def
             apply fastforce   
            using frees good_interp osafe by auto
        done
      then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s)"
        by presburger
      have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s) "
        using mkv mkva by auto
      note mkvt = main_eq[of t]
      have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
          (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
        = (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)"
        using IH[OF fsafe frees] by auto
      have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        ((mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)
        =(mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>))"
        subgoal for s
          using NFU frees fsafe good_interp mk_v_agree osubst_preserves_ODE_vars uadmit_fml_ntadjoint
          using agree by blast
        done
      have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
        (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) = (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) "
        using main_eq by auto
      have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
         (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
          =  (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)"
        using fml_eq1 fml_eq2 fml_eq3 by meson
      have sem_eq:"\<And>t. ODE_sem I (OsubstFO ODE \<sigma>) (sol t) = ODE_sem (adjointFO I \<sigma> (sol t, b)) ODE (sol t)"
        subgoal for t
          using nsubst_ode[OF good_interp osafe NOU frees, of "(sol t,b)"] by auto
        done
      have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (sol s) = ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE (sol s)"
        subgoal for s
          using nsubst_ode[OF good_interp osafe NOU frees, of "(sol s, b)"]
          uadmit_ode_ntadjoint'[OF frees good_interp agrees[of s] osafe]
          by auto
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
         {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta by (rule sem_fact[of ta])
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)}"
        using fml_eq rangeI t sol solves_ode_domainD by fastforce
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
 {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto
      show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..ta}
                 {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sola 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>})"
        apply(rule exI[where x=sol])
        apply(rule conjI)
         subgoal by (rule refl)
        apply(rule exI[where x=t])
        apply(rule conjI)
         subgoal using  mkvt t by auto
        apply(rule conjI)
         subgoal by (rule t)
        subgoal by (rule sol'') 
        done
  next
    fix b 
      and sol::"real \<Rightarrow> (real, 'sz) vec" 
      and t::real
    assume eq1:"\<nu> = (sol 0, b)"
    assume eq2:"\<omega> = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol t)"
    assume t:"0 \<le> t"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
     {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
    have agree_sem:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>)))"
      subgoal for t
        using mk_v_agree[of I "OsubstFO ODE \<sigma>" "(sol 0, b)" "sol t"] unfolding Vagree_def apply auto
        done
      done
    have bv_sub:"(-BVO ODE) \<subseteq> - (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>))"
      by(induction ODE, auto) 
    have agree:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- BVO ODE)"
      using agree_sub[OF bv_sub agree_sem] by auto
    \<comment> \<open>Necessary\<close>
    have mkv:"\<And>t. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol t, b)) ODE (sol 0, b) (sol t)"
      using nsubst_mkv[OF good_interp NOU osafe frees]
      by auto
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (-(BVO ODE))"
      using ODE_bound_effect sol
      by (metis osubst_preserves_ODE_vars)
    have FVT_sub:"(\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<subseteq> (-(BVO ODE))"
      using NOU NO_to_NOU unfolding OUadmitFO_def by fastforce
    have agrees:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (\<Union>y\<in>{y. Inl (Inr y) \<in> SIGO ODE}. FVT (\<sigma> y))" 
      subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE  = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE"
      subgoal for s
        apply (rule uadmit_mkv_ntadjoint)
           prefer 3
           using NOU hmm[of s] NO_to_NOU unfolding OUadmitFO_def Vagree_def
           apply fastforce   
          using frees good_interp osafe by auto
        done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
      = (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)"
      using IH[OF fsafe frees] by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)
      =(mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>))"
        using  NFU frees fsafe good_interp mk_v_agree osubst_preserves_ODE_vars uadmit_fml_ntadjoint agree by blast
      
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
     (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) = (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) "
     using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
       =  (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)"
      using fml_eq1 fml_eq2 fml_eq3 by meson
     have sem_eq:"\<And>t. ODE_sem I (OsubstFO ODE \<sigma>) (sol t) = ODE_sem (adjointFO I \<sigma> (sol t, b)) ODE (sol t)"
       subgoal for t
         using nsubst_ode[OF good_interp osafe NOU frees, of "(sol t,b)"] by auto
       done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (sol s) = ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE (sol s)"
      subgoal for s
        using nsubst_ode[OF good_interp osafe NOU frees, of "(sol s, b)"]
        uadmit_ode_ntadjoint'[OF frees good_interp agrees[of s] osafe]
        by auto
      done
    have sol':"
      (sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t}  {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta using sem_fact[of ta] by auto
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol'':"(sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t} {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      using sub fml_eq by blast
    show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol t) = mk_v I (OsubstFO ODE \<sigma>) (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..ta} {x. mk_v I (OsubstFO ODE \<sigma>) (sola 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)})"
      apply(rule exI[where x=sol])
      apply(rule conjI)
       subgoal by (rule refl)
      apply(rule exI[where x=t])
      apply(rule conjI)
       subgoal using t mkvt by auto
      apply(rule conjI)
       subgoal by (rule t)
      subgoal by (rule sol'')
      done
    qed
  qed
  then show ?case by auto 
next
  case (NPadmit_Assign \<sigma> \<theta> x)
  then show ?case using nsubst_dterm[OF good_interp, of \<sigma> \<theta>] by auto
next
  case (NPadmit_DiffAssign \<sigma> \<theta> x)
  then show ?case using nsubst_dterm[OF good_interp, of \<sigma> \<theta>] by auto
next
  case (NFadmit_Geq \<sigma> \<theta>1 \<theta>2)
  then show ?case 
    using nsubst_dterm[OF good_interp, of \<sigma> \<theta>1] 
    using nsubst_dterm[OF good_interp, of \<sigma> \<theta>2] by auto
next
  case (NFadmit_Prop \<sigma> args f)
  assume NTA:"\<And>i. TadmitFO \<sigma> (args i)"
  have "\<And>\<nu>.  fsafe ($\<phi> f args) \<Longrightarrow>  (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<nu> \<in> fml_sem I (FsubstFO ($\<phi> f args) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) ($\<phi> f args))"
  proof -
    fix \<nu>
    assume safe:"fsafe ($\<phi> f args)"
    from safe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    assume subFree:"(\<And>i. dsafe (\<sigma> i))"
    have vec_eq:"(\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>) = (\<chi> i. dterm_sem I (TsubstFO (args i) \<sigma>) \<nu>)"
      apply(rule vec_extensionality)
      using nsubst_dterm[OF good_interp NTA safes subFree] by auto
    then show "?thesis \<nu>" unfolding adjointFO_def by auto
  qed
  then show ?case by auto 
next
  case (NPadmit_Sequence \<sigma> a b) then 
  have PUA:"PUadmitFO \<sigma> b (BVP (PsubstFO a \<sigma>))"
    and PA:"NPadmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b))"
    and hpsafeS:"hpsafe (PsubstFO a \<sigma>)"
     by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PsubstFO a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu> , OF hpsafeS] by auto
      done
    have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b) =
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
      subgoal for \<mu>
      proof -
        assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>)"
        show "((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
          using uadmit_prog_ntadjoint [OF PUA agree[OF assm] ssafe safe2 good_interp] 
          by auto
      qed
      done      
    have "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PsubstFO b \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
      using IH2[OF safe2 ssafe] by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b)"
      using sem_eq by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b)"
      using IH1[OF safe1 ssafe] by auto
    ultimately
    show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a ;; b))"
      by auto
  qed
  then show ?case by auto
next
  case (NPadmit_Loop \<sigma> a) then 
  have PA:"NPadmit \<sigma> a"
    and PUA:"PUadmitFO \<sigma> a (BVP (PsubstFO a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and hpsafeS:"hpsafe (PsubstFO a \<sigma>)"
      by auto
  have "hpsafe (a**) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PsubstFO a \<sigma>))"
      subgoal for \<nu> \<mu>
        using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu>, OF hpsafeS] 
        by auto
      done
    have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a) =
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) a)"
      subgoal for \<nu> \<mu> \<omega> 
        proof -
          assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>)"
          show "((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) a)"
            using uadmit_prog_ntadjoint[OF PUA agree[OF assm] ssafe hpsafe  good_interp] by auto
        qed
      done 
    fix \<nu> \<omega>
    have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
      by auto
    have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PsubstFO a \<sigma>)) ^^ n))"
      using rtrancl_is_UN_relpow by auto
    moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PsubstFO a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n)))"
    proof -
      fix n
      show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PsubstFO a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (PsubstFO a \<sigma>)"] relpow[of n "prog_sem (adjointFO I \<sigma> \<nu>) a"])
          apply(unfold relcomp_unfold)
          apply auto
           subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
              using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
              apply (metis (no_types, lifting)) 
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
           done
          subgoal for ab b
            apply(rule exI[where x=ab])
            apply(rule exI[where x=b])
            using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting))
            using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
            apply (metis (no_types, lifting))
          done
        done
      qed
      qed
    moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PsubstFO a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n))"
      apply(rule UN_rule)
      using eachEq by auto
    moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (adjointFO I \<sigma> \<nu>) a) ^^ n))"
       using rtrancl_is_UN_relpow by auto
    ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**))"
      by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and FUA:"FUadmitFO \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>)  (Exists x \<phi>)))"
  proof -
    assume fsafe:"fsafe (Exists x \<phi>)"
    from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    fix \<nu>
    have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
      unfolding Vagree_def by auto
    have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> (repv \<nu> x r)) \<phi>) =
                      ((repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe' good_interp] by auto
    have "(\<nu> \<in> fml_sem I (FsubstFO  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (FsubstFO \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> (repv \<nu> x r)) \<phi>)"
      using IH[OF fsafe' ssafe] by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using sem_eq by auto
    moreover have "... = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
    ultimately show "(\<nu> \<in> fml_sem I (FsubstFO  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Diamond \<sigma> \<phi> a) then 
  have PA:"NPadmit \<sigma> a" 
    and FUA:"FUadmitFO \<sigma> \<phi> (BVP (PsubstFO a \<sigma>))"
    and IH1:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and IH2:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and hpsafeF:"hpsafe (PsubstFO a \<sigma>)"
      by auto
  have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
  proof -
    assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
    fix \<nu>
    have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(PsubstFO a \<sigma>))"
      using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu>, OF hpsafeF] by auto
    have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        (\<omega> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>) =
        (\<omega> \<in> fml_sem (adjointFO I \<sigma> \<omega>) \<phi>)"
      using uadmit_fml_ntadjoint [OF FUA agree ssafe fsafe' good_interp] by auto
    have "(\<nu> \<in> fml_sem I (FsubstFO (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> \<omega> \<in> fml_sem I (FsubstFO \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjointFO I \<sigma> \<omega>) \<phi>)"
      using IH1[OF fsafe' ssafe] IH2[OF hpsafe ssafe, of \<nu>] by auto
    moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using sem_eq IH2 hpsafe ssafe by blast
    moreover have "... = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>))"
      by auto
    ultimately show "?thesis \<nu>" by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Context \<sigma> \<phi> C) then
  have FA:"NFadmit \<sigma> \<phi>"
    and FUA:"FUadmitFO \<sigma> \<phi> UNIV"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
      by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow>
           (\<And>i. dsafe (\<sigma> i))\<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"\<And>i. dsafe (\<sigma> i)"
    fix \<nu>
    have Ieq:" Contexts (adjointFO I \<sigma> \<nu>) C = Contexts I C"
      unfolding adjointFO_def by auto
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe good_interp] by auto
    then have sem:"fml_sem I (FsubstFO \<phi> \<sigma>) =  fml_sem (adjointFO I \<sigma> \<nu>) \<phi>"
      using IH' agree adj_eq by auto
    show "?thesis \<nu>"  using Ieq sem by auto
  qed
  then show ?case by auto
qed (auto)

lemma nsubst_fml:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  assumes good_interp:"is_interp I"
  assumes NFA:"NFadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes frees:"(\<forall>i. dsafe (\<sigma> i))"
  shows "(\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
  using good_interp NFA fsafe frees 
  by (auto simp add: nsubst_hp_fml)

lemma nsubst_hp:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  assumes good_interp:"is_interp I"    
  assumes NPA:"NPadmit \<sigma> \<alpha>"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes frees:"\<And>i. dsafe (\<sigma> i)"
  shows "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in>  prog_sem (adjointFO I \<sigma> \<nu>) \<alpha>)"
 using good_interp NPA hpsafe frees nsubst_hp_fml by blast

lemma psubst_sterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"    
  shows "(sterm_sem I \<theta> = sterm_sem (PFadjoint I \<sigma>) \<theta>)"
proof (induction \<theta>)
qed (auto simp add: PFadjoint_def)

lemma psubst_dterm:
  fixes I::"('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"    
  shows "(dsafe \<theta> \<Longrightarrow> dterm_sem I \<theta> = dterm_sem (PFadjoint I \<sigma>) \<theta>)"
proof (induction \<theta>)
  case (Differential \<theta>)
  assume safe:"dsafe (Differential \<theta>)"
  from safe have free:"dfree \<theta>" by auto
  assume sem:"dsafe \<theta> \<Longrightarrow> dterm_sem I \<theta> = dterm_sem (PFadjoint I \<sigma>) \<theta>"
  have "\<And>\<nu>. frechet I \<theta> (fst \<nu>) (snd \<nu>) = frechet (PFadjoint I \<sigma>) \<theta> (fst \<nu>) (snd \<nu>)"
    apply(rule sterm_determines_frechet)
        using good_interp free apply auto
     subgoal unfolding is_interp_def PFadjoint_def by auto
    using psubst_sterm[of I \<theta>] by auto
  then show "?case"
    by (auto simp add: directional_derivative_def)
 qed (auto simp add: PFadjoint_def)
    
lemma psubst_ode:
assumes good_interp:"is_interp I"
shows "ODE_sem I ODE = ODE_sem (PFadjoint I \<sigma>) ODE"
proof (induction "ODE")
  case (OVar x)
  then show ?case unfolding PFadjoint_def by auto
next
  case (OSing x1a x2)
  then show ?case apply auto apply (rule ext) apply (rule vec_extensionality) using psubst_sterm[OF good_interp, of x2 \<sigma>]  by auto 
next
  case (OProd ODE1 ODE2)
  then show ?case by auto
qed
  
lemma psubst_fml:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"    
shows "(PPadmit \<sigma> \<alpha>  \<longrightarrow> hpsafe \<alpha> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. (\<nu>,\<omega>) \<in> prog_sem I (PPsubst \<alpha> \<sigma>) = ((\<nu>,\<omega>) \<in> prog_sem (PFadjoint I \<sigma>) \<alpha>))) \<and> 
  (PFadmit \<sigma> \<phi> \<longrightarrow> fsafe \<phi> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. \<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)))"
proof (induction rule: PPadmit_PFadmit.induct)
  case (PPadmit_ODE \<sigma> \<phi> ODE)
  assume PF:"PFadmit \<sigma> \<phi>"
  assume PFU:"PFUadmit \<sigma> \<phi> (BVO ODE)"
  assume IH:"fsafe \<phi> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>))"
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>
  (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (EvolveODE ODE \<phi>)))"
  proof -
    assume safe:"hpsafe (EvolveODE ODE \<phi>)"
    from safe have fsafe:"fsafe \<phi>" by auto
    assume ssafe:"(\<forall>i. fsafe (\<sigma> i))"
    have fml_eq:"\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)"
      using IH ssafe fsafe by auto
    fix \<nu> \<omega>
    show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (EvolveODE ODE \<phi>))"
      apply auto
    proof -
      fix b sol t
      assume eq1:"\<nu> = (sol 0, b)"
        and eq2:"\<omega> = mk_v I ODE (sol 0, b) (sol t)"
        and t:"0 \<le> t"
        and sol:"(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
      have var:"ODE_vars I ODE =  ODE_vars (PFadjoint I \<sigma>) ODE"
        by(induction ODE, auto simp add: PFadjoint_def)
      have mkv_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I ODE (sol 0, b) (sol s) = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol s)"
        apply(rule agree_UNIV_eq)
        unfolding Vagree_def apply auto
         subgoal for s i
           using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
           unfolding Vagree_def var 
           apply (cases "Inl i \<in> Inl ` ODE_vars I ODE", auto simp add: var)
            by force
        subgoal for s i
          using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
          unfolding Vagree_def var 
          apply (cases "Inr i \<in> Inr ` ODE_vars I ODE", auto simp add: var psubst_ode)
           using psubst_ode[OF good_interp, of ODE \<sigma>] apply auto
          using psubst_ode[OF good_interp, of ODE \<sigma>] by force
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..t}
       {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta using psubst_ode[OF good_interp, of ODE \<sigma>] by auto
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma> ) \<phi>)}"
        subgoal for s
          using solves_ode_domainD[OF sol, of s] mkv_eq[of s] fml_eq[of "mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) (sol s)"]
          by auto
        done
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (PFadjoint I \<sigma> ) ODE)) {0..t}
        {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma> ) \<phi>}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto          
      show"\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v I ODE (sol 0, b) (sol t) = mk_v (PFadjoint I \<sigma>) ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..ta}
               {x. mk_v (PFadjoint I \<sigma>) ODE (sola 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>})"
        apply(rule exI[where x=sol])
        apply(rule conjI)
         apply(rule refl)
        apply(rule exI[where x=t])
        apply(rule conjI)
         subgoal using mkv_eq t by auto
        apply(rule conjI)
         apply(rule t)
        apply(rule sol'') 
        done
    next
      fix b sol t
      assume eq1:"\<nu> = (sol 0, b)"
        and eq2:"\<omega> = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol t)"
        and t:"0 \<le> t"
        and sol:"(sol solves_ode (\<lambda>a. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..t} {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>}"
      have var:"ODE_vars I ODE =  ODE_vars (PFadjoint I \<sigma>) ODE"
        by(induction ODE, auto simp add: PFadjoint_def)
      have mkv_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I ODE (sol 0, b) (sol s) = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol s)"
        apply(rule agree_UNIV_eq)
        unfolding Vagree_def apply auto
         subgoal for s i
           using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
           unfolding Vagree_def var 
           apply (cases "Inl i \<in> Inl ` ODE_vars I ODE", auto simp add: var)
            by force
        subgoal for s i
          using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
          unfolding Vagree_def var 
          apply (cases "Inr i \<in> Inr ` ODE_vars I ODE", auto simp add: var psubst_ode)
           using psubst_ode[OF good_interp, of ODE \<sigma>] apply auto
          using psubst_ode[OF good_interp, of ODE \<sigma>] by force
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t}
         {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta using psubst_ode[OF good_interp, of ODE \<sigma>] by auto
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v  I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>))}"
        subgoal for s
          using solves_ode_domainD[OF sol, of s] mkv_eq[of s] fml_eq[of "mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) (sol s)"]
          by auto
        done
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem I ODE)) {0..t}
        {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto
      show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol t) = mk_v I ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and> (sola solves_ode (\<lambda>a. ODE_sem I ODE)) {0..ta} {x. mk_v I ODE (sola 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)})"
        apply(rule exI[where x=sol])
        by (metis dual_order.refl intervalE mkv_eq sol'' t)
    qed
  qed
  then show ?case
    by auto
next
  case (PPadmit_Assign \<sigma> x \<theta>)
  have "hpsafe (x := \<theta>) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (x := \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (x := \<theta>)))"
  proof -
    assume safe:"hpsafe (x := \<theta>)"
    then have dsafe:"dsafe \<theta>" by auto
    assume safes:"(\<forall>i. fsafe (\<sigma> i))"
    show "?thesis"
      using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
  qed
  then show "?case" by auto 
next
  case (PPadmit_DiffAssign \<sigma> x \<theta>)
  have "hpsafe (DiffAssign x \<theta>) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (DiffAssign x \<theta>) \<sigma>)) = (((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (DiffAssign x \<theta>))))"
  proof -
    assume safe:"hpsafe (DiffAssign x \<theta>)"
    then have dsafe:"dsafe \<theta>" by auto
    assume safes:"(\<forall>i. fsafe (\<sigma> i))"
    show "?thesis"
      using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
   qed
  then show ?case by auto
next
  case (PFadmit_Geq \<sigma> \<theta>1 \<theta>2) then 
  have "fsafe (Geq \<theta>1 \<theta>2) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu>. (\<nu> \<in> fml_sem I (PFsubst (Geq \<theta>1 \<theta>2) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) (Geq \<theta>1 \<theta>2)))"
  proof -
    assume safe:"fsafe (Geq \<theta>1 \<theta>2)"
    then have safe1:"dsafe \<theta>1" 
      and safe2:"dsafe \<theta>2" by auto
    assume safes:"(\<forall>i. fsafe (\<sigma> i))"
    show "?thesis"
      using psubst_dterm[OF good_interp safe1, of \<sigma>] psubst_dterm[OF good_interp safe2, of \<sigma>] by  auto
  qed
  then show ?case by auto
next
  case (PFadmit_Prop \<sigma> p args) then
  have "fsafe (Prop p args) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (PFsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) ($\<phi> p args)))"
  proof -
    assume safe:"fsafe (Prop p args)" and ssafe:" (\<And>i. fsafe (\<sigma> i))"
    fix \<nu>
    from safe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    have Ieq:"Predicates I p = Predicates (PFadjoint I \<sigma>) p"
      unfolding PFadjoint_def by auto
    have vec:"(\<chi> i. dterm_sem I (args i) \<nu>) = (\<chi> i. dterm_sem (PFadjoint I \<sigma>) (args i) \<nu>)"
      apply(auto simp add: vec_eq_iff)
      subgoal for i using safes[of i] 
        by (metis good_interp psubst_dterm)
      done
    show "?thesis \<nu>" using  Ieq vec by auto
  qed
  then show "?case" by auto
next
  case (PPadmit_Sequence \<sigma> a b) then 
  have PUA:"PPUadmit \<sigma> b (BVP (PPsubst a \<sigma>))"
    and PA:"PPadmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a))"
    and IH2:"hpsafe b \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b))"
    and substSafe:"hpsafe (PPsubst a \<sigma>)"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF substSafe] by auto
      done
    have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b) =
        ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
      subgoal for \<mu>
      proof -
        assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>)"
        show "((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b) = ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
          using PUA agree[OF assm] safe2 ssafe good_interp by auto
      qed
      done      
    have "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PPsubst b \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
      using IH2[OF safe2 ssafe] by blast 
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (PFadjoint I \<sigma>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
      using IH1[OF safe1 ssafe] sem_eq by blast
    ultimately
    show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a ;; b))"
      by auto
  qed
  then show ?case by auto
next
  case (PPadmit_Loop \<sigma> a) then 
  have PA:"PPadmit \<sigma> a"
  and PUA:"PPUadmit \<sigma> a (BVP (PPsubst a \<sigma>))"
  and IH:"hpsafe a \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a))"
  and substSafe:"hpsafe (PPsubst a \<sigma>)"   
    by auto
  have "hpsafe (a**) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"\<And>i. fsafe (\<sigma> i)"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
      subgoal for \<nu> \<mu>
        using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF substSafe] by auto
      done
    fix \<nu> \<omega>
    have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
      by auto
    have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PPsubst a \<sigma>)) ^^ n))"
      using rtrancl_is_UN_relpow by auto
    moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (PFadjoint I \<sigma>) a)^^ n)))"
    proof -
      fix n
      show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (PFadjoint I \<sigma>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (PPsubst a \<sigma>)"] relpow[of n "prog_sem (PFadjoint I \<sigma>) a"])
          apply(unfold relcomp_unfold)
          apply auto
           subgoal for ab b
              apply(rule exI[where x=ab])
              apply(rule exI[where x=b])
              using IH2 IH[OF hpsafe ssafe]  by auto
          subgoal for ab b
            apply(rule exI[where x=ab])
            apply(rule exI[where x=b])
            using IH2 IH[OF hpsafe ssafe] by auto
        done
      qed
    qed
    moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PPsubst a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (PFadjoint I \<sigma>) a)^^ n))"
      apply(rule UN_rule)
      using eachEq by auto
    moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (PFadjoint I \<sigma>) a) ^^ n))"
       using rtrancl_is_UN_relpow by auto
    ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**))"
      by auto
  qed
  then show ?case by auto
next
next
  case (PFadmit_Context \<sigma> \<phi> C) then
  have FA:"PFadmit \<sigma> \<phi>"
    and FUA:"PFUadmit \<sigma> \<phi> UNIV"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>))"
    by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow>
           (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
    fix \<nu> :: "(real, 'sz) vec \<times> (real, 'sz) vec"
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    then have sem:"fml_sem I (PFsubst \<phi> \<sigma>) =  fml_sem (PFadjoint I \<sigma>) \<phi>"
      using IH' agree  by auto
    show "?thesis \<nu>"  using sem 
      apply auto
      apply(cases C)
        unfolding PFadjoint_def apply auto
      apply(cases C)
       by auto
  qed
  then show ?case by auto
qed (auto simp add: PFadjoint_def)

lemma subst_ode:
  fixes I:: "('sf, 'sc, 'sz) interp" and \<nu> :: "'sz state"
  assumes good_interp:"is_interp I"
  shows "osafe ODE \<Longrightarrow> 
         ssafe \<sigma> \<Longrightarrow> 
         Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow>
         ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE (fst \<nu>)"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case unfolding adjoint_def by (cases "SODEs \<sigma> c", auto)
next
  case (osafe_Sing \<theta> x)
  then show ?case 
    using subst_sterm [of  \<sigma> \<theta> I "\<nu>"]
    unfolding ssafe_def by auto
next
  case (osafe_Prod ODE1 ODE2) then
  have NOU1:"Oadmit \<sigma> ODE1  (BVO (OProd ODE1 ODE2))" and NOU2:"Oadmit \<sigma> ODE2  (BVO (OProd ODE1 ODE2))" 
    by auto
  have TUA_sub:"\<And>\<sigma> \<theta> A B. TUadmit \<sigma> \<theta> B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> TUadmit \<sigma> \<theta> A"
    unfolding TUadmit_def by auto
  have OA_sub:"\<And>ODE A B. Oadmit \<sigma> ODE B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Oadmit \<sigma> ODE A"
    subgoal for ODE A B
    proof (induction rule: Oadmit.induct)
      case (Oadmit_Var \<sigma> c U)
      then show ?case by auto
    next
      case (Oadmit_Sing \<sigma> \<theta> U x)
      then show ?case using TUA_sub[of \<sigma> \<theta> U A] by auto
    next
      case (Oadmit_Prod \<sigma> ODE1 U ODE2)
      then show ?case by auto
    qed
    done
  have sub1:"(BVO ODE1) \<subseteq> (BVO (OProd ODE1 ODE2))"
    by auto
  have sub2: "(BVO ODE2) \<subseteq> (BVO (OProd ODE1 ODE2))"
    by auto
  have "ODE_sem I (Osubst ODE1 \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE1 (fst \<nu>)"
    "ODE_sem I (Osubst ODE2 \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE2 (fst \<nu>)" using osafe_Prod.IH osafe_Prod.prems osafe_Prod.hyps
    using OA_sub[OF NOU1 sub1] OA_sub[OF NOU2 sub2] by auto
  then show ?case by auto
qed

lemma osubst_eq_ODE_vars: "ODE_vars I (Osubst ODE \<sigma>) = ODE_vars (adjoint I \<sigma> \<nu>) ODE"
proof (induction ODE)
  case (OVar x)
  then show ?case by (cases "SODEs \<sigma> x", auto simp add: adjoint_def)
qed (auto)

lemma subst_semBV:"semBV (adjoint I \<sigma> \<nu>') ODE = (semBV I (Osubst ODE \<sigma>))"
proof (induction ODE)
  case (OVar x)
  then show ?case by (cases "SODEs \<sigma> x", auto simp add: adjoint_def)
qed (auto)

lemma subst_mkv:
  fixes I::"('sf, 'sc, 'sz) interp"
  fixes \<nu>::"'sz state"
  fixes \<nu>'::"'sz state"
  assumes good_interp:"is_interp I"  
  assumes NOU:"Oadmit \<sigma> ODE (BVO ODE)"
  assumes osafe:"osafe ODE "
  assumes frees:"ssafe \<sigma>"
  shows "(mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) 
    = (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>'))"
  apply(rule agree_UNIV_eq)
  using mk_v_agree[of "adjoint I \<sigma> \<nu>'" "ODE" \<nu> "fst \<nu>'"]
  using mk_v_agree[of "I" "Osubst ODE \<sigma>" \<nu> "fst \<nu>'"] 
  unfolding Vagree_def 
  using subst_ode[OF good_interp osafe  frees NOU, of \<nu>'] 
  apply auto
   subgoal for i
     apply(erule allE[where x=i])+
     apply(cases "Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<nu>') ODE")
      using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>']
      apply force
   proof -
     assume "ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>') = ODE_sem (local.adjoint I \<sigma> \<nu>') ODE (fst \<nu>')"
       "Inl i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE \<and> Inl i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE \<longrightarrow>
       fst (mk_v (local.adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i = fst \<nu> $ i"
       "Inl i \<notin> Inl ` ODE_vars I (Osubst ODE \<sigma>) \<and> Inl i \<notin> Inr ` ODE_vars I (Osubst ODE \<sigma>) \<longrightarrow>
       fst (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = fst \<nu> $ i"
       "Inl i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE"
     then show
        "fst (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = fst (mk_v (local.adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i"
         using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>'] by force
   qed
  subgoal for i
    apply(erule allE[where x=i])+
    apply(cases "Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<nu>') ODE")
     using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>']
     apply force
  proof -
    assume "ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>') = ODE_sem (local.adjoint I \<sigma> \<nu>') ODE (fst \<nu>')"
      "Inr i \<notin> Inl ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE \<and> Inr i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE \<longrightarrow>
      snd (mk_v (local.adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i = snd \<nu> $ i"
      "Inr i \<notin> Inl ` ODE_vars I (Osubst ODE \<sigma>) \<and> Inr i \<notin> Inr ` ODE_vars I (Osubst ODE \<sigma>) \<longrightarrow>
      snd (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = snd \<nu> $ i"
      "Inr i \<notin> Inr ` ODE_vars (local.adjoint I \<sigma> \<nu>') ODE"
    then show "snd (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = snd (mk_v (local.adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i"
      using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>'] by force
  qed
done 
  
lemma subst_fml_hp:
  fixes I::"('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"
  shows 
  "(Padmit \<sigma> \<alpha> \<longrightarrow>
    (hpsafe \<alpha> \<longrightarrow>
     ssafe \<sigma> \<longrightarrow>
    (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) \<alpha>))))
    \<and>
    (Fadmit \<sigma> \<phi> \<longrightarrow>
    (fsafe \<phi> \<longrightarrow>
    ssafe \<sigma> \<longrightarrow>
    (\<forall> \<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))))"
proof (induction rule: Padmit_Fadmit.induct)
  case (Padmit_Pvar \<sigma> a) then
  have "hpsafe ($\<alpha> a) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst ($\<alpha> a) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) ($\<alpha> a)))"
    apply (cases "SPrograms \<sigma> a")
     unfolding adjoint_def by auto
  then show ?case by auto
next
  case (Padmit_Sequence \<sigma> a b) then 
  have PUA:"PUadmit \<sigma> b (BVP (Psubst a \<sigma>))"
    and PA:"Padmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b))"
    and substSafe:"hpsafe (Psubst a \<sigma>)"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"ssafe \<sigma>"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
      done
    have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b) =
        ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) b)"
      subgoal for \<mu>
      proof -
        assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
        show "((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) b)"
          using uadmit_prog_adjoint[OF PUA agree[OF assm] safe2 ssafe good_interp] by auto
      qed
      done      
    have "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) b)"
      using IH2[OF safe2 ssafe] by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b)"
      using sem_eq by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b)"
      using IH1[OF safe1 ssafe] by auto
    ultimately
    show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a ;; b))"
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_Loop \<sigma> a) then 
  have PA:"Padmit \<sigma> a"
    and PUA:"PUadmit \<sigma> a (BVP (Psubst a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
    and substSafe:"hpsafe (Psubst a \<sigma>)"
    by auto
  have "hpsafe (a**) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
    subgoal for \<nu> \<mu>
      using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
    done
  have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
      ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a) =
      ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) a)"
    subgoal for \<nu> \<mu> \<omega> 
    proof -
      assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
      show "((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) a)"
        using uadmit_prog_adjoint[OF PUA agree[OF assm] hpsafe ssafe good_interp] by auto
    qed
    done 
  fix \<nu> \<omega>
  have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
    by auto
  have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (Psubst a \<sigma>)) ^^ n))"
    using rtrancl_is_UN_relpow by auto
  moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (Psubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjoint I \<sigma> \<nu>) a)^^ n)))"
  proof -
    fix n
    show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (Psubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjoint I \<sigma> \<nu>) a)^^ n)))"
    proof (induct n)
      case 0
      then show ?case by auto
    next
      case (Suc n) then
      have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a ^^ n)"
        by auto
      have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
        using relpow.simps(2) relpow_commute by metis
      show ?case 
        apply (simp only: relpow[of n "prog_sem I (Psubst a \<sigma>)"] relpow[of n "prog_sem (adjoint I \<sigma> \<nu>) a"])
        apply(unfold relcomp_unfold)
        apply auto
         subgoal for ab b
            apply(rule exI[where x=ab])
            apply(rule exI[where x=b])
            using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
            using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
            apply (metis (no_types, lifting)) 
          done
        subgoal for ab b
          apply(rule exI[where x=ab])
          apply(rule exI[where x=b])
          using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
           using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
           apply (metis (no_types, lifting))
          using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
          apply (metis (no_types, lifting))
        done
      done
    qed
  qed
  moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (Psubst a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (adjoint I \<sigma> \<nu>) a)^^ n))"
    apply(rule UN_rule)
    using eachEq by auto
  moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (adjoint I \<sigma> \<nu>) a) ^^ n))"
     using rtrancl_is_UN_relpow by auto
  ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a**))"
    by auto
   qed
  then show ?case by auto
next
  case (Padmit_ODE \<sigma> ODE \<phi>) then
  have OA:"Oadmit \<sigma> ODE (BVO ODE)"
    and FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> (BVO ODE)"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
      by auto
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>
     ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (EvolveODE ODE \<phi>)))"
  proof (auto)
    fix aa ba bb
      and sol :: "real \<Rightarrow>(real, 'sz) vec" 
      and t :: real
    assume ssafe:"ssafe \<sigma>"
    assume osafe:"osafe ODE"
    assume fsafe:"fsafe \<phi>"
    assume t:"0 \<le> t"
    assume eq:"(aa,ba) = mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t)"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} 
      {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
    have silly:"
      \<And>t. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (local.adjoint I \<sigma> (sol t, bb)) ODE (sol 0, bb) (sol t)"
      subgoal for t using subst_mkv[OF good_interp OA osafe ssafe, of "(sol 0, bb)" "(sol t, bb)"] by auto done
    have hmmsubst:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO (Osubst ODE \<sigma>)))"
      subgoal for s
        apply (rule ODE_bound_effect[of s])
         apply auto[1]
        by (rule sol)
      done
    have sub:"(-(BVO ODE)) \<subseteq> (-(BVO (Osubst ODE \<sigma>)))"
      by(induction ODE, auto)
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO ODE))"
      subgoal for s
        using agree_sub[OF sub hmmsubst[of s]] by auto
      done
    from hmm have hmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO ODE))}"
      unfolding VSagree_def Vagree_def by auto
    note hmmm = hmmsubst
    from hmmm have hmmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO (Osubst ODE \<sigma>)))}"
      unfolding VSagree_def Vagree_def by auto
    have Vagree_of_VSagree:"\<And>\<nu>1 \<nu>2 \<omega>1 \<omega>2 S. VSagree \<nu>1 \<nu>2 {x. Inl x \<in> S} \<Longrightarrow> VSagree \<omega>1 \<omega>2 {x. Inr x \<in> S} \<Longrightarrow> Vagree (\<nu>1, \<omega>1) (\<nu>2, \<omega>2) S"
      unfolding VSagree_def Vagree_def by auto
    have mkv:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s)"
      subgoal for s by (rule silly[of s])
      done
    have lem:"\<And>ODE. Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (-(BVO ODE))"
      subgoal for ODE
        apply(induction rule: Oadmit.induct)
          apply auto
        subgoal for \<sigma> \<theta> U x xa
          apply (cases "SFunctions \<sigma> xa")
           apply auto
          unfolding TUadmit_def
        proof -
          fix a
          assume un:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
          assume sig:"xa \<in> SIGT \<theta>"
          assume some:"SFunctions \<sigma> xa = Some a"
          assume fvt:"x \<in> FVT a"
          assume xU:"x \<in> U"
          from un sig have "(case SFunctions \<sigma> xa of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
            by auto 
          then have "(FVT a) \<inter> U = {}"
           using some by auto
          then show "False" using fvt xU by auto
        qed
        done
      done
    have FVT_sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (-(BVO ODE))"
      using lem[OF OA] by auto
    have agrees: "\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)"
       subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol 0, bb)) ODE = mk_v (adjoint I \<sigma> (sol s, bb)) ODE"
      subgoal for s         
        apply (rule uadmit_mkv_adjoint)
           prefer 3
          subgoal using agrees by auto
         using OA hmm[of s] unfolding  Vagree_def
        using ssafe good_interp osafe by auto
      done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
      = (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV I (Osubst ODE \<sigma>))"
      subgoal for s
        using mk_v_agree[of I "Osubst ODE \<sigma>" "(sol 0,bb)" "sol s"] osubst_eq_ODE_vars[of I ODE \<sigma>]
        unfolding Vagree_def
        by auto
      done
    have sembv_eq:"semBV I (Osubst ODE \<sigma>) = semBV (adjoint I \<sigma> (sol 0, bb)) ODE"
      using subst_semBV by auto
    have fml_vagree':"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV (adjoint I \<sigma> (sol 0,bb)) ODE)"
      using sembv_eq fml_vagree by auto
    have mysub:"-BVO ODE \<subseteq> -(semBV I (Osubst ODE \<sigma>))"
      by(induction ODE,auto)
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- BVO ODE)"
      subgoal for s using agree_sub[OF mysub fml_vagree[of s]] by auto done
    have fml_sem_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi> = fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>"
      apply (rule uadmit_fml_adjoint)
          using FUA fsafe ssafe  good_interp fml_vagree by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)
      =(mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>))"
      using fml_sem_eq by auto
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) = (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) "
      using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
       =  (mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)"
      using fml_eq1 fml_eq2 fml_eq3 by meson
    have sem_eq:"\<And>t. ODE_sem I (Osubst ODE \<sigma>) (sol t) = ODE_sem (adjoint I \<sigma> (sol t, bb)) ODE (sol t)"
      subgoal for t
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol t,bb)"] by auto
      done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (Osubst ODE \<sigma>) (sol s) = ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE (sol s)"
      subgoal for s
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol s, bb)"]
        uadmit_ode_adjoint'[OF ssafe good_interp agrees[of s] osafe] 
        by auto
      done
    have sol':"(sol solves_ode (\<lambda>_. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
       {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta by (rule sem_fact[of ta])
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
{x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      using sub by auto
    show "\<exists>sola. sol 0 = sola 0 \<and>
      (\<exists>ta. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (local.adjoint I \<sigma> (sol 0, bb)) ODE (sola 0, bb) (sola ta) \<and>
            0 \<le> ta \<and>
            (sola solves_ode (\<lambda>a. ODE_sem (local.adjoint I \<sigma> (sol 0, bb)) ODE)) {0..ta}
             {x. mk_v (local.adjoint I \<sigma> (sol 0, bb)) ODE (sola 0, bb) x \<in> fml_sem (local.adjoint I \<sigma> (sol 0, bb)) \<phi>})"
    apply(rule exI[where x=sol])
    apply(rule conjI)
     subgoal by (rule refl)
    apply(rule exI[where x=t])
    apply(rule conjI)
     subgoal using  mkvt t by auto
    apply(rule conjI)
     subgoal by (rule t)
    subgoal by (rule sol'') 
    done
  next
    fix aa ba bb 
      and sol::"real \<Rightarrow> (real, 'sz) vec" 
      and t::real
    assume ssafe:"ssafe \<sigma>"
    assume osafe:"osafe ODE"
    assume fsafe:"fsafe \<phi>"
      
    assume eq:"(aa,ba) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol t)"
    assume t:"0 \<le> t"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
    {x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
    have silly:"
      \<And>t. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (local.adjoint I \<sigma> (sol t, bb)) ODE (sol 0, bb) (sol t)"
      subgoal for t using subst_mkv[OF good_interp OA osafe ssafe, of "(sol 0, bb)" "(sol t, bb)"] by auto done
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO ODE))"
      subgoal for s
        apply (rule ODE_bound_effect[of s])
         apply auto[1]
        by (rule sol)
      done
    from hmm have hmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO ODE))}"
      unfolding VSagree_def Vagree_def by auto
    have Vagree_of_VSagree:"\<And>\<nu>1 \<nu>2 \<omega>1 \<omega>2 S. VSagree \<nu>1 \<nu>2 {x. Inl x \<in> S} \<Longrightarrow> VSagree \<omega>1 \<omega>2 {x. Inr x \<in> S} \<Longrightarrow> Vagree (\<nu>1, \<omega>1) (\<nu>2, \<omega>2) S"
      unfolding VSagree_def Vagree_def by auto
    have mkv:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s)"
      subgoal for s by (rule silly[of s])
      done
    have lem:"\<And>ODE. Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (-(BVO ODE))"
      subgoal for ODE
        apply(induction rule: Oadmit.induct)
        apply auto
        subgoal for \<sigma> \<theta> U x xa
        apply (cases "SFunctions \<sigma> xa")
         apply auto
        unfolding TUadmit_def
     proof -
       fix a
       assume un:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
       assume sig:"xa \<in> SIGT \<theta>"
       assume some:"SFunctions \<sigma> xa = Some a"
       assume fvt:"x \<in> FVT a"
       assume xU:"x \<in> U"
       from un sig have "(case SFunctions \<sigma> xa of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
         by auto 
       then have "(FVT a) \<inter> U = {}"
        using some by auto
       then show "False" using fvt xU by auto
     qed
       done
     done
    have FVT_sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (-(BVO ODE))"
      using lem[OF OA] by auto
    have agrees: "\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)"
       subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol 0, bb)) ODE = mk_v (adjoint I \<sigma> (sol s, bb)) ODE"
      subgoal for s         
        apply (rule uadmit_mkv_adjoint)
           prefer 3
          subgoal using agrees by auto
         using OA hmm[of s] unfolding  Vagree_def
        using ssafe good_interp osafe by auto
      done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
      = (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV I (Osubst ODE \<sigma>))"
      subgoal for s
        using mk_v_agree[of I "Osubst ODE \<sigma>" "(sol 0,bb)" "sol s"] osubst_eq_ODE_vars[of I ODE \<sigma>]
        unfolding Vagree_def
        by auto
      done
    have sembv_eq:"semBV I (Osubst ODE \<sigma>) = semBV (adjoint I \<sigma> (sol 0, bb)) ODE"
      using subst_semBV by auto
    have fml_vagree':"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV (adjoint I \<sigma> (sol 0,bb)) ODE)"
      using sembv_eq fml_vagree by auto
    have mysub:"-BVO ODE \<subseteq> -(semBV I (Osubst ODE \<sigma>))"
      by(induction ODE,auto)
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- BVO ODE)"
      subgoal for s using agree_sub[OF mysub fml_vagree[of s]] by auto done
    have fml_sem_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi> = fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>"
      apply (rule uadmit_fml_adjoint)
      using FUA fsafe ssafe  good_interp fml_vagree by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)
      =(mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>))"
      using fml_sem_eq by auto
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) = (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) "
      using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
         (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
          =  (mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)"
         using fml_eq1 fml_eq2 fml_eq3 by meson
    have sem_eq:"\<And>t. ODE_sem I (Osubst ODE \<sigma>) (sol t) = ODE_sem (adjoint I \<sigma> (sol t, bb)) ODE (sol t)"
      subgoal for t
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol t,bb)"] by auto
      done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (Osubst ODE \<sigma>) (sol s) = ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE (sol s)"
      subgoal for s
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol s, bb)"]
        uadmit_ode_adjoint'[OF ssafe good_interp agrees[of s] osafe] 
        by auto
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol':"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} {x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta using sem_fact[of ta] by auto
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sol'':"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      subgoal for ta using sub[of ta] apply auto 
        by (meson empty_iff)
      done
  show "\<exists>sola. sol 0 = sola 0 \<and>
        (\<exists>ta. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol t) = mk_v I (Osubst ODE \<sigma>) (sola 0, bb) (sola ta) \<and>
              0 \<le> ta \<and>
              (sola solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..ta} {x. mk_v I (Osubst ODE \<sigma>) (sola 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)})"
    apply(rule exI[where x=sol])
    apply(rule conjI)
     subgoal by (rule refl)
    apply(rule exI[where x=t])
    apply(rule conjI)
     subgoal using  mkvt t by auto
    apply(rule conjI)
     subgoal by (rule t)
    subgoal using sol'' by auto 
    done
  qed
  then show "?case" by auto 
next
  case (Padmit_Choice \<sigma> a b) then 
  have IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b))"
    by blast+
  have hpsafe1:"hpsafe (a \<union>\<union> b) \<Longrightarrow> hpsafe a" 
    and hpsafe2:"hpsafe (a \<union>\<union> b) \<Longrightarrow> hpsafe b" 
    by (auto dest: hpsafe.cases)
  show ?case using IH1[OF hpsafe1] IH2[OF hpsafe2] by auto
next
  case (Padmit_Assign \<sigma> \<theta> x) then
  have TA:"Tadmit \<sigma> \<theta>" by auto
  have "hpsafe (Assign x \<theta>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (Assign x \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (Assign x \<theta>)))"
  proof -
    assume hpsafe:"hpsafe (Assign x \<theta>)"
    assume ssafe:"ssafe \<sigma>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
        unfolding ssafe_def by auto
    from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
    fix \<nu> \<omega>
    show "?thesis \<nu> \<omega>"
      using subst_dterm[OF good_interp TA dsafe ssafes]
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_DiffAssign \<sigma> \<theta> x) then
  have TA:"Tadmit \<sigma> \<theta>" by auto
  have "hpsafe (DiffAssign x \<theta>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (DiffAssign x \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (DiffAssign x \<theta>)))"
  proof -
    assume hpsafe:"hpsafe (DiffAssign x \<theta>)"
    assume ssafe:"ssafe \<sigma>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
        unfolding ssafe_def by auto
    from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
    fix \<nu> \<omega>
    show "?thesis \<nu> \<omega>"
      using subst_dterm[OF good_interp TA dsafe ssafes]
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_Test \<sigma> \<phi>) then
  have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    by auto
  have "hpsafe (? \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (? \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (? \<phi>)))"
  proof -
    assume hpsafe:"hpsafe (? \<phi>)"
    from hpsafe have fsafe:"fsafe \<phi>" by (auto dest: hpsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu> \<omega>
    show "?thesis \<nu> \<omega>" using IH[OF fsafe ssafe] by auto
  qed
  then show ?case by auto
next
  case (Fadmit_Geq \<sigma> \<theta>1 \<theta>2) then 
  have TA1:"Tadmit \<sigma> \<theta>1" and TA2:"Tadmit \<sigma> \<theta>2"
    by auto
  have "fsafe (Geq \<theta>1 \<theta>2) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (Geq \<theta>1 \<theta>2) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (Geq \<theta>1 \<theta>2)))"
  proof -
    assume fsafe:"fsafe (Geq \<theta>1 \<theta>2)"
    assume ssafe:"ssafe \<sigma>"
    from fsafe have dsafe1:"dsafe \<theta>1" and dsafe2:"dsafe \<theta>2"
      by (auto dest: fsafe.cases)
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      unfolding ssafe_def by auto
    fix \<nu>
    show "?thesis \<nu>" using 
      subst_dterm[OF good_interp TA1 dsafe1 ssafes]
      subst_dterm[OF good_interp TA2 dsafe2 ssafes]
      by auto 
  qed
  then show ?case by auto 
next 
  case (Fadmit_Prop1 \<sigma> args p p') then
    have TA:"\<And>i. Tadmit \<sigma> (args i)"
    and some:"SPredicates \<sigma> p = Some p'"
    and NFA:"NFadmit (\<lambda>i. Tsubst (args i) \<sigma>) p'"
    and substSafes:"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
      by auto
    have "fsafe ($\<phi> p args) \<Longrightarrow>
         ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
    proof -
      assume fsafe:"fsafe ($\<phi> p args)"
      assume ssafe:"ssafe \<sigma>"
      from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      unfolding ssafe_def by auto
      fix \<nu>
      from fsafe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
      have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
          dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
        using  subst_dterm[OF good_interp TA safes ssafes] by auto
      have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
        by (auto simp add: IH safes)
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have freef:"fsafe p'" using ssafe some unfolding ssafe_def by auto 
      have IH2:"(\<nu> \<in> fml_sem I (FsubstFO p' ?sub)) = (\<nu> \<in> fml_sem (adjointFO I ?sub \<nu>) p')"
        using nsubst_fml good_interp NFA freef substSafes
        by blast
      have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
        apply(auto simp add: vec_eq_iff)
        subgoal for i
          using IH[of i, OF safes[of i]] 
          by auto
        done
      show "?thesis \<nu>" 
        using IH safes eqs apply (auto simp add:  IH2  some good_interp)
        using some unfolding adjoint_def adjointFO_def by auto
    qed
  then show "?case" by auto
next
  case (Fadmit_Prop2 \<sigma> args p) 
  note TA = Fadmit_Prop2.hyps(1)
    and none = Fadmit_Prop2.hyps(2)
  have "fsafe (Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
  proof -
    assume safe:"fsafe (Prop p args)" and ssafe:"ssafe \<sigma>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
        unfolding ssafe_def by auto
    fix \<nu>
    from safe have  safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
    using  subst_dterm[OF good_interp TA safes ssafes] by auto
    have Ieq:"Predicates I p = Predicates (adjoint I \<sigma> \<nu>) p"
      using none unfolding adjoint_def by auto
    have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
      apply(auto simp add: vec_eq_iff)
      subgoal for i using IH[of i, OF safes[of i]] by auto
      done
    show "?thesis \<nu>" using none IH Ieq vec by auto
  qed
  then show "?case" by auto
next
  case (Fadmit_Not \<sigma> \<phi>) then 
  have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    by blast
  have fsafe:"fsafe (Not \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  show ?case using IH[OF fsafe] by auto
next
  case (Fadmit_And \<sigma> \<phi> \<psi>) then
    have IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
      and IH2:"fsafe \<psi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<psi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<psi>))"
      by (blast)+
    have fsafe1:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<phi>" and fsafe2:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<psi>" 
      by (auto dest: fsafe.cases)
    show ?case using IH1[OF fsafe1] IH2[OF fsafe2] by auto
next
  case (Fadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    and FUA:"FUadmit \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>)  (Exists x \<phi>)))"
  proof -
    assume fsafe:"fsafe (Exists x \<phi>)"
    from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu>
    have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
      unfolding Vagree_def by auto
    have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> (repv \<nu> x r)) \<phi>) =
                      ((repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
      using uadmit_fml_adjoint[OF FUA agree fsafe' ssafe good_interp] by auto
    have "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (Fsubst \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> (repv \<nu> x r)) \<phi>)"
      using IH[OF fsafe' ssafe] by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
      using sem_eq by auto
    moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
    ultimately show "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>)  (Exists x \<phi>))"
      by auto
    qed
  then show ?case by auto
next
  case (Fadmit_Diamond \<sigma> \<phi> a) then 
    have PA:"Padmit \<sigma> a" 
      and FUA:"FUadmit \<sigma> \<phi> (BVP (Psubst a \<sigma>))"
      and IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      and IH2:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
      and substSafe:"hpsafe (Psubst a \<sigma>)"
      by auto
    have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
    proof -
      assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
      assume ssafe:"ssafe \<sigma>"
      from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
      fix \<nu>
      have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(Psubst a \<sigma>))"
        using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
      have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
          (\<omega> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>) =
          (\<omega> \<in> fml_sem (local.adjoint I \<sigma> \<omega>) \<phi>)"
        using uadmit_fml_adjoint[OF FUA agree fsafe' ssafe good_interp] by auto
      have "(\<nu> \<in> fml_sem I (Fsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<and> \<omega> \<in> fml_sem I (Fsubst \<phi> \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjoint I \<sigma> \<omega>) \<phi>)"
        using IH1[OF fsafe' ssafe] IH2[OF hpsafe ssafe, of \<nu>] by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
        using sem_eq IH2 hpsafe ssafe by blast
      moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>))"
        by auto
      ultimately show "?thesis \<nu>" by auto
    qed
  then show ?case by auto
next
   case (Fadmit_Prop1 \<sigma> args p p') 
   have "fsafe(Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
   proof -
     assume fsafe:"fsafe (Prop p args)"
       and ssafe:"ssafe \<sigma>"
     from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
       "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
       unfolding ssafe_def by auto
     fix \<nu>
     note TA = Fadmit_Prop1.hyps(1)
       and some = Fadmit_Prop1.hyps(2) and NFA = Fadmit_Prop1.hyps(3)
     from fsafe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
     have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
         dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
       using  subst_dterm[OF good_interp TA safes ssafes] by auto
     have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
       by (auto simp add: IH safes)
     let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
     have subSafe:"(\<forall> i. dsafe (?sub i))"
       by (simp add: safes ssafes tsubst_preserves_safe)
     have freef:"fsafe p'" using ssafe some unfolding ssafe_def by auto 
     have IH2:"(\<nu> \<in> fml_sem I (FsubstFO p' ?sub)) = (\<nu> \<in> fml_sem (adjointFO I ?sub \<nu>) p')"
       by (simp add: nsubst_fml [OF good_interp NFA freef subSafe])
     have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
       apply(auto simp add: vec_eq_iff)
       subgoal for i
         using IH[of i, OF safes[of i]] 
         by auto
       done
     show "?thesis \<nu>" 
       using IH safes eqs apply (auto simp add:  IH2  some good_interp)
       using some unfolding adjoint_def adjointFO_def by auto
   qed    
next
  case (Fadmit_Context1 \<sigma> \<phi> C C') then
  have FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> UNIV"
    and some:"SContexts \<sigma> C = Some C'"
    and PFA:"PFadmit (\<lambda>_. Fsubst \<phi> \<sigma>) C'"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    and substSafe:"fsafe(Fsubst \<phi> \<sigma>)"
    by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    from safe have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu> :: "'sz state"
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
    have eq:"(\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
      using adj_eq IH[OF fsafe ssafe] by auto
    let ?sub = "(\<lambda>_. Fsubst \<phi> \<sigma>)"
    let ?R1 = "fml_sem I (Fsubst \<phi> \<sigma>)"
    let ?R2 = "fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
    have eq':"?R1 = ?R2"
      using adj_eq IH[OF fsafe ssafe] by auto
    have freef:"fsafe C'" using ssafe some unfolding ssafe_def by auto 
    have IH2:"(\<nu> \<in> fml_sem I (PFsubst C' ?sub)) = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
      using psubst_fml good_interp PFA fsafe substSafe freef by blast 
    have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      using IH[OF fsafe ssafe] by auto
    then have IH:"fml_sem I (Fsubst \<phi> \<sigma>) = fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
      using eq' by blast
    have duh:" (\<lambda>f' _. fml_sem I (case () of () \<Rightarrow> Fsubst \<phi> \<sigma>)) = (\<lambda> x (). fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
      by (simp add: case_unit_Unity eq' ext)
    have extend_PF:"(PFadjoint I ?sub) = (extendc I ?R2)"
      unfolding PFadjoint_def using IH apply (simp)
      by (metis old.unit.case old.unit.exhaust)
    have "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem I (PFsubst C' (\<lambda>_. Fsubst \<phi> \<sigma>)))"
      using some by simp
    moreover have "... = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
      using IH2 by auto
    moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R2) C')"
      using extend_PF by simp
    moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R1) C')"
      using eq' by auto
    moreover have "... = (\<nu> \<in> Contexts (adjoint I \<sigma> \<nu>) C (fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      using some unfolding adjoint_def apply auto
      apply (simp add: eq' local.adjoint_def)
      by (simp add: eq' local.adjoint_def)
    moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
      by auto
    ultimately
    show "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
      by blast
  qed
  then show ?case by auto
next
  case (Fadmit_Context2 \<sigma> \<phi> C) then
  have FA:"Fadmit \<sigma> \<phi>"
  and FUA:"FUadmit \<sigma> \<phi> UNIV"
  and none:"SContexts \<sigma> C = None"
  and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow>
           ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu>
    have Ieq:" Contexts (local.adjoint I \<sigma> \<nu>) C = Contexts I C"
      using none unfolding adjoint_def by auto
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
    then have sem:"fml_sem I (Fsubst \<phi> \<sigma>) =  fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>"
      using IH' agree adj_eq by auto
    show "?thesis \<nu>"  using none Ieq sem by auto
  qed
  then show ?case by auto
qed

lemma subst_fml:
  fixes I::"('sf, 'sc, 'sz) interp" and \<nu>::"'sz state"
  assumes good_interp:"is_interp I"
  assumes Fadmit:"Fadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  shows "(\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using subst_fml_hp[OF good_interp] Fadmit fsafe ssafe by blast
    
lemma subst_fml_valid:
  fixes I::"('sf, 'sc, 'sz) interp" and \<nu>::"'sz state"
  assumes Fadmit:"Fadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  assumes valid:"valid \<phi>"
  shows "valid (Fsubst \<phi> \<sigma>)"
proof -
  have sub_sem:"\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)"
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good_interp:"is_interp I"
    have good_adj:"is_interp (adjoint I \<sigma> \<nu>)"
      apply(rule adjoint_safe[OF good_interp])
      using ssafe unfolding ssafe_def by auto
    have \<phi>sem:"\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>" using valid using good_adj unfolding valid_def by blast
    then show "?thesis I \<nu>"
      using subst_fml[OF good_interp Fadmit fsafe ssafe]
      by auto
  qed
  then show ?thesis unfolding valid_def by blast 
qed
  

lemma subst_sequent:
  fixes I::"('sf, 'sc, 'sz) interp" and \<nu>::"'sz state"
  assumes good_interp:"is_interp I"
  assumes Sadmit:"Sadmit \<sigma> (\<Gamma>,\<Delta>)"
  assumes Ssafe:"Ssafe (\<Gamma>,\<Delta>)"
  assumes ssafe:"ssafe \<sigma>"
  shows "(\<nu> \<in> seq_sem I (Ssubst (\<Gamma>,\<Delta>) \<sigma>)) = (\<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) (\<Gamma>,\<Delta>))"
proof -
  let ?f = "(seq2fml (\<Gamma>, \<Delta>))"
  have subst_eqG:"Fsubst (foldr (&&) \<Gamma> TT) \<sigma> = foldr (&&) (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Gamma>) TT"
    by(induction \<Gamma>, auto simp add: TT_def)
  have subst_eqD:"Fsubst (foldr (||) \<Delta> FF) \<sigma> = foldr (||) (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Delta>) FF"
    by(induction \<Delta>, auto simp add: FF_def Or_def)
  have subst_eq:"Fsubst ?f \<sigma> = (seq2fml (Ssubst (\<Gamma>, \<Delta>) \<sigma>))"
    using subst_eqG subst_eqD 
    by (auto simp add: Implies_def Or_def)
  have fsafeG:"fsafe (foldr (&&) \<Gamma> TT)" 
    using Ssafe apply(induction \<Gamma>, auto simp add: Ssafe_def TT_def)
    by fastforce
  have fsafeD:"fsafe (foldr (||) \<Delta> FF)" 
    using Ssafe Or_def apply(induction \<Delta>, auto simp add: Ssafe_def FF_def Or_def)
    by fastforce
  have fsafe:"fsafe ?f" 
    using fsafeD fsafeG by (auto simp add: Implies_def Or_def)
  have FadmitG:"Fadmit \<sigma> (foldr (&&) \<Gamma> TT)"
    using Sadmit Or_def apply(induction \<Gamma>, auto simp add: Sadmit_def TT_def Or_def)
    by fastforce
  have FadmitD:"Fadmit \<sigma> (foldr (||) \<Delta> FF)"
    using Sadmit Or_def apply(induction \<Delta>, auto simp add: Sadmit_def FF_def Or_def)
    by fastforce
  have Fadmit:"Fadmit \<sigma> ?f" 
    using FadmitG FadmitD unfolding Implies_def
    by (simp add: Implies_def Or_def)
  have "(\<nu> \<in> fml_sem I (Fsubst ?f \<sigma>)) 
       =(\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (seq2fml (\<Gamma>, \<Delta>)))"
    using subst_fml[OF good_interp Fadmit fsafe ssafe]
    by auto
  then show ?thesis
    using subst_eq by auto
  qed

subsection \<open>Soundness of substitution rule\<close>
theorem subst_rule:
  assumes sound:"sound R"
  assumes Radmit:"Radmit \<sigma> R"
  assumes FVS:"FVS \<sigma> = {}"
  assumes Rsafe:"Rsafe R"
  assumes ssafe:"ssafe \<sigma>"
  shows "sound (Rsubst R \<sigma>)"
proof -
  obtain SG and C where Rdef:"R = (SG,C)" by (cases R, auto)
  obtain SG' and C' where Rdef':"Rsubst R \<sigma> = (SG',C')" by (cases R, auto)
  obtain \<Gamma>C and \<Delta>C where Cdef:"C = (\<Gamma>C, \<Delta>C)" by (cases C, auto)
  obtain \<Gamma>C' and \<Delta>C' where C'def:"C' = (\<Gamma>C', \<Delta>C')" by (cases C', auto)
  have CC':"(Ssubst (\<Gamma>C, \<Delta>C) \<sigma>) = (\<Gamma>C', \<Delta>C')"
    using Rdef Rdef' Cdef C'def by auto
  have "\<And>I \<nu>. is_interp I \<Longrightarrow> (\<And>\<Gamma> \<Delta> \<omega>  . List.member SG' (\<Gamma>, \<Delta>) \<Longrightarrow> \<omega> \<in> seq_sem I (\<Gamma>, \<Delta>)) \<Longrightarrow> \<nu> \<in> seq_sem I C'"
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good_interp:"is_interp I"
    assume prems:"(\<And>\<Gamma> \<Delta> \<omega>. List.member SG' (\<Gamma>, \<Delta>) \<Longrightarrow> \<omega> \<in> seq_sem I (\<Gamma>, \<Delta>))"
    have good_interp':"\<And>\<omega>. is_interp (adjoint I \<sigma> \<omega>)"
      using adjoint_safe[OF good_interp ] ssafe[unfolded ssafe_def] by auto
    have sound:"\<And>\<omega>. (\<And>\<phi> \<nu> . List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem (adjoint I \<sigma> \<omega>) \<phi>) \<Longrightarrow> \<omega> \<in> seq_sem (adjoint I \<sigma> \<omega>) (\<Gamma>C, \<Delta>C)"
      using soundD_memv[of SG C] sound good_interp' Rdef Cdef by auto
    have SadmitC:"Sadmit \<sigma> (\<Gamma>C, \<Delta>C)" 
      using Radmit unfolding Radmit_def Rdef Cdef by auto
    have SsafeC:"Ssafe (\<Gamma>C, \<Delta>C)" 
      using Rsafe unfolding Rsafe_def Rdef Cdef by auto
    have seq_sem:"\<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) (\<Gamma>C, \<Delta>C)"
    proof(rule sound)
      fix S :: "('sf,'sc,'sz) sequent" and \<nu>'
      assume mem:"List.member SG S"
      obtain \<Gamma>S \<Delta>S where Sdef:"S = (\<Gamma>S, \<Delta>S)" by (cases S, auto)
      from mem obtain di where di:"di < length SG \<and> SG ! di = S"
      by (meson in_set_conv_nth in_set_member)
      have SadmitS:"Sadmit \<sigma> (\<Gamma>S, \<Delta>S)"
        using Rdef Sdef di Radmit Radmit_def by auto
      have SsafeS:"Ssafe (\<Gamma>S, \<Delta>S)"
        using Rsafe unfolding Rsafe_def Rdef Cdef using Sdef mem di by auto
      have map_mem:"\<And>f L x. List.member L x \<Longrightarrow> List.member (map f L) (f x)"
        subgoal for f L x 
          by (induction L, auto simp add: member_rec)
        done
      let ?S' = "(Ssubst (\<Gamma>S, \<Delta>S) \<sigma>)"
      have eq:"Ssubst S \<sigma> = (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Gamma>S, map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Delta>S)" 
        using Sdef by auto
      from Sdef have mem':"List.member SG' (fst ?S', snd ?S')"
        using mem Rdef Rdef' eq map_mem[of SG S "(\<lambda>x. Ssubst x \<sigma>)"] by auto
      have "\<nu>' \<in> seq_sem I (fst ?S', snd ?S')" by (rule prems[OF mem', of \<nu>'])
      then have "\<nu>' \<in> seq_sem (adjoint I \<sigma> \<nu>') S"
        using subst_sequent[OF good_interp SadmitS SsafeS ssafe, of \<nu>']
        Sdef by auto
      have VA:"Vagree \<nu> \<nu>' (FVS \<sigma>)" using FVS unfolding Vagree_def by auto
      show "\<nu>' \<in> seq_sem (local.adjoint I \<sigma> \<nu>) S"
        using adjoint_consequence VA ssafe[unfolded ssafe_def]
        by (metis \<open>\<nu>' \<in> seq_sem (local.adjoint I \<sigma> \<nu>') S\<close> dfree_is_dsafe)
      qed
    have "\<nu> \<in> seq_sem I (\<Gamma>C', \<Delta>C')"
      using subst_sequent[OF good_interp SadmitC SsafeC ssafe, of \<nu>] seq_sem Cdef C'def CC'
      by auto
    then show  "\<nu> \<in> seq_sem I C'" using C'def by auto
    qed
  then show ?thesis
    apply(rule soundI_memv')
      using Rdef' by auto
qed

end end
