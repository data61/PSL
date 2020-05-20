theory "Uniform_Renaming" 
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
begin context ids begin

section \<open>Uniform and Bound Renaming\<close>
text \<open>Definitions and soundness proofs for the renaming rules Uniform Renaming and Bound Renaming.
Renaming in dL swaps the names of two variables x and y, as in the swap operator of Nominal Logic.
\<close>
fun swap ::"'sz \<Rightarrow> 'sz \<Rightarrow> 'sz \<Rightarrow> 'sz"
where "swap x y z = (if z = x then  y else if z = y then x else z)"
 
subsection \<open>Uniform Renaming Definitions\<close>

primrec TUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm"
where 
  "TUrename x y (Var z) = Var (swap x y z)"
| "TUrename x y (DiffVar z) = DiffVar (swap x y z)"
| "TUrename x y (Const r) = (Const r)"
| "TUrename x y (Function f args) = Function f (\<lambda>i. TUrename x y (args i))"
| "TUrename x y (Plus \<theta>1 \<theta>2) = Plus (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Times \<theta>1 \<theta>2) = Times (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Differential \<theta>) = Differential (TUrename x y \<theta>)"
  
primrec OUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) ODE \<Rightarrow> ('sf, 'sz) ODE"
where
  "OUrename x y (OVar c) = undefined"
| "OUrename x y (OSing z \<theta>) = OSing (swap x y z) (TUrename x y \<theta>)"
| "OUrename x y (OProd ODE1 ODE2) = OProd (OUrename x y ODE1) (OUrename x y ODE2)"
  
inductive ORadmit :: "('sf, 'sz) ODE \<Rightarrow> bool"
where
  ORadmit_Sing:"ORadmit (OSing x \<theta>)"
| ORadmit_Prod:"ORadmit ODE1 \<Longrightarrow> ORadmit ODE2 \<Longrightarrow> ORadmit (OProd ODE1 ODE2)"
  
primrec PUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) hp \<Rightarrow> ('sf, 'sc, 'sz) hp"
  and   FUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula"
where
  "PUrename x y (Pvar a) = undefined"
| "PUrename x y (Assign z \<theta>) = Assign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (DiffAssign z \<theta>) = DiffAssign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (Test \<phi>) = Test (FUrename x y \<phi>)"
| "PUrename x y (EvolveODE ODE \<phi>) = EvolveODE (OUrename x y ODE) (FUrename x y \<phi>)"
| "PUrename x y (Choice a b) = Choice (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Sequence a b) = Sequence (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Loop a) = Loop (PUrename x y a)"

| "FUrename x y (Geq \<theta>1 \<theta>2) = Geq (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "FUrename x y (Prop p args) = Prop p (\<lambda>i. TUrename x y (args i))"
| "FUrename x y (Not \<phi>) = Not (FUrename x y \<phi>)"
| "FUrename x y (And \<phi> \<psi>) = And (FUrename x y \<phi>) (FUrename x y \<psi>)"
| "FUrename x y (Exists z \<phi>) = Exists (swap x y z) (FUrename x y \<phi>)"
| "FUrename x y (Diamond \<alpha> \<phi>) = Diamond (PUrename x y \<alpha>) (FUrename x y \<phi>)"
| "FUrename x y (InContext C \<phi>) = undefined"

subsection \<open>Uniform Renaming Admissibility\<close>

inductive PRadmit :: "('sf, 'sc, 'sz) hp \<Rightarrow> bool"
  and     FRadmit ::"('sf, 'sc, 'sz) formula \<Rightarrow> bool"
where
  PRadmit_Assign:"PRadmit (Assign x \<theta>)"
| PRadmit_DiffAssign:"PRadmit (DiffAssign x \<theta>)"
| PRadmit_Test:"FRadmit \<phi> \<Longrightarrow> PRadmit (Test \<phi>)"
| PRadmit_EvolveODE:"ORadmit ODE \<Longrightarrow> FRadmit \<phi> \<Longrightarrow> PRadmit (EvolveODE ODE \<phi>)"
| PRadmit_Choice:"PRadmit a \<Longrightarrow> PRadmit b \<Longrightarrow> PRadmit (Choice a b)"
| PRadmit_Sequence:"PRadmit a \<Longrightarrow> PRadmit b \<Longrightarrow> PRadmit (Sequence a b)"
| PRadmit_Loop:"PRadmit a \<Longrightarrow> PRadmit (Loop a)"

| FRadmit_Geq:"FRadmit (Geq \<theta>1 \<theta>2)"
| FRadmit_Prop:"FRadmit (Prop p args)"
| FRadmit_Not:"FRadmit \<phi> \<Longrightarrow> FRadmit (Not \<phi>)"
| FRadmit_And:"FRadmit \<phi> \<Longrightarrow> FRadmit \<psi> \<Longrightarrow> FRadmit (And \<phi> \<psi>)"
| FRadmit_Exists:"FRadmit \<phi> \<Longrightarrow> FRadmit (Exists x \<phi>)"
| FRadmit_Diamond:"PRadmit \<alpha> \<Longrightarrow> FRadmit \<phi> \<Longrightarrow> FRadmit (Diamond \<alpha> \<phi>)"

inductive_simps
    FRadmit_box_simps[simp]: "FRadmit (Box a f)"
and PRadmit_box_simps[simp]: "PRadmit (Assign x e)"

definition RSadj :: "'sz \<Rightarrow> 'sz \<Rightarrow> 'sz simple_state \<Rightarrow> 'sz simple_state"
where "RSadj x y \<nu> = (\<chi> z. \<nu> $ (swap x y z))" 

definition Radj :: "'sz \<Rightarrow> 'sz \<Rightarrow> 'sz state \<Rightarrow> 'sz state"
where "Radj x y \<nu> = (RSadj x y (fst \<nu>), RSadj x y (snd \<nu>))" 

lemma SUren: "sterm_sem I (TUrename x y \<theta>) \<nu> = sterm_sem I \<theta> (RSadj x y \<nu>)"
  by (induction \<theta>, auto simp add: RSadj_def)

lemma ren_preserves_dfree:"dfree \<theta> \<Longrightarrow> dfree (TUrename x y \<theta>)"
  by(induction rule: dfree.induct, auto intro: dfree.intros)

subsection \<open>Uniform Renaming Soundness Proof and Lemmas\<close>

lemma TUren_frechet:
  assumes good_interp:"is_interp I"
  shows "dfree \<theta> \<Longrightarrow> frechet I (TUrename x y \<theta>) \<nu> \<nu>' = frechet I \<theta> (RSadj x y \<nu>) (RSadj x y \<nu>')"
proof (induction rule: dfree.induct)
  \<comment> \<open>There's got to be a more elegant proof of this...\<close>
  case (dfree_Var i)
  then show ?case 
    unfolding RSadj_def apply auto 
       subgoal by (metis vec_lambda_eta)
      subgoal
      proof (auto simp add: axis_def)
        assume yx:"y \<noteq> x"
        have a:"(\<chi> z. \<nu>' $ (if z = x then y else if z = y then x else z)) $ y = \<nu>' $ x"
         by simp
       show "\<nu>' \<bullet> (\<chi> i. if i = x then 1 else 0) 
                 = (\<chi> z. \<nu>' $ (if z = x then y else if z = y then x else z)) \<bullet> (\<chi> i. if i = y then 1 else 0)"
         by (metis (no_types) a axis_def inner_axis)
      qed
     subgoal
     proof -
       have "\<And>v s. v \<bullet> (\<chi> sa. if sa = (s::'sz) then 1 else 0) = v $ s"
         subgoal for v s
           using inner_axis[of v s 1]
           by (auto simp add: axis_def)
         done
       then show ?thesis
         by (auto simp add: axis_def)
     qed
    subgoal
    proof -
      assume a1: "i \<noteq> y"
      assume a2: "i \<noteq> x"
      have "\<And>v s. v \<bullet> (\<chi> sa. if sa = (s::'sz) then 1 else 0) = v $ s"
        by (metis (no_types) inner_axis axis_def inner_prod_eq)
      then show ?thesis
        using a2 a1 by (auto simp add: axis_def)
    qed
    done 
qed (auto simp add: SUren good_interp is_interp_def)

lemma RSadj_fst:"RSadj x y (fst \<nu>) = fst (Radj x y \<nu>)"
  unfolding RSadj_def Radj_def by auto

lemma RSadj_snd:"RSadj x y (snd \<nu>) = snd (Radj x y \<nu>)"
  unfolding RSadj_def Radj_def by auto

lemma TUren:
  assumes good_interp:"is_interp I"
  shows "dsafe \<theta> \<Longrightarrow> dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>)"
proof (induction rule: dsafe.induct)
  case (dsafe_Diff \<theta>)
  assume free:"dfree \<theta>"
  show ?case 
    apply (auto simp add: directional_derivative_def)
    using TUren_frechet[OF good_interp free, of x y "fst \<nu>" "snd \<nu>"]
     by (auto simp add: RSadj_fst RSadj_snd)
qed (auto simp add: Radj_def RSadj_def)

lemma adj_sum:"RSadj x y (\<nu>1 + \<nu>2) = (RSadj x y \<nu>1) + (RSadj x y \<nu>2)"
  unfolding RSadj_def apply auto apply (rule vec_extensionality)
  subgoal for i
    apply (cases "i = x")
     apply (cases "i = y")
      by auto
  done

lemma OUren: "ORadmit ODE \<Longrightarrow> ODE_sem I (OUrename x y ODE) \<nu> = RSadj x y (ODE_sem I ODE (RSadj x y \<nu>))"
proof (induction rule: ORadmit.induct)
  case (ORadmit_Prod ODE1 ODE2)
  then show ?case 
    using adj_sum by auto
next
  case (ORadmit_Sing z \<theta>)
  then show ?case 
    by (rule vec_extensionality | auto simp add: SUren RSadj_def)+   
qed

lemma state_eq: 
  fixes \<nu> \<nu>' :: "'sz state"
  shows "(\<And>i. (fst \<nu>) $ i = (fst \<nu>') $ i) \<Longrightarrow> (\<And>i. (snd \<nu>) $ i = (snd \<nu>') $ i) \<Longrightarrow> \<nu>  = \<nu>'"
  apply (cases "\<nu>", cases "\<nu>'", auto)
   by(rule vec_extensionality, auto)+
  
lemma Radj_repv1:
  fixes x y z ::"'sz" 
  shows "(Radj x y (repv \<nu> y r)) = repv (Radj x y \<nu>) x r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y") 
       unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
      unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repv2:
  fixes x y z ::"'sz" 
  shows "(Radj x y (repv \<nu> x r)) = repv (Radj x y \<nu>) y r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y") 
       unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
      unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repv3:
  fixes x y z ::"'sz" 
  assumes zx:"z \<noteq> x" and zy:"z \<noteq> y"
  shows "(Radj x y (repv \<nu> z r)) = repv (Radj x y \<nu>) z r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y") 
       using zx zy unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
      using zx zy unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repd1:
  fixes x y z ::"'sz" 
  shows "(Radj x y (repd \<nu> y r)) = repd (Radj x y \<nu>) x r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y") 
       unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
      unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repd2:
  fixes x y z ::"'sz" 
  shows "(Radj x y (repd \<nu> x r)) = repd (Radj x y \<nu>) y r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y") 
       unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
      unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repd3:
  fixes x y z ::"'sz" 
  assumes zx:"z \<noteq> x" and zy:"z \<noteq> y"
  shows "(Radj x y (repd \<nu> z r)) = repd (Radj x y \<nu>) z r"
  apply(rule state_eq)
   subgoal for i
     apply(cases "i = x") apply (cases "i = y")
     using zx zy unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    using zx zy unfolding Radj_def RSadj_def by auto
  done

\<comment> \<open>i.e. shows \<open>Radj x y\<close> is a bijection for all \<open>x y\<close>\<close>
lemma Radj_eq_iff:"(a = b) = ((Radj x y a) = (Radj x y b))"
  unfolding Radj_def RSadj_def apply auto
  apply (rule state_eq)
   apply smt+
  done

lemma RSadj_cancel:"RSadj x y (RSadj x y \<nu>) = \<nu>"
  unfolding RSadj_def apply auto
  apply(rule vec_extensionality)
  by(auto)

lemma Radj_cancel:"Radj x y (Radj x y \<nu>) = \<nu>"
  unfolding Radj_def RSadj_def apply auto
  apply(rule state_eq)
   subgoal for i by(cases "i = x", cases "i = y", auto)
  subgoal for i by(cases "i = x", cases "i = y", auto)
  done

lemma OUrename_preserves_ODE_vars:"ORadmit ODE \<Longrightarrow> {z. (swap x y z) \<in> ODE_vars I ODE} = ODE_vars I (OUrename x y ODE)"
  apply(induction rule: ORadmit.induct)
   subgoal for xa \<theta> by auto
  subgoal for ODE1 ODE2
  proof -
    assume IH1:"{z. swap x y z \<in> ODE_vars I ODE1} = ODE_vars I (OUrename x y ODE1)"
    assume IH2:"{z. swap x y z \<in> ODE_vars I ODE2} = ODE_vars I (OUrename x y ODE2)"
    have "{z. swap x y z \<in> ODE_vars I (OProd ODE1 ODE2)} =
          {z. swap x y z \<in> (ODE_vars I ODE1 \<union> ODE_vars I ODE2)}" by auto
    moreover have "... = {z. swap x y z \<in> (ODE_vars I ODE1)} \<union> {z. swap x y z \<in> (ODE_vars I ODE2)}" by auto
    moreover have "... = ODE_vars I (OUrename x y ODE1) \<union> ODE_vars I (OUrename x y ODE2)" using IH1 IH2 by auto
    moreover have "... = ODE_vars I (OUrename x y (OProd ODE1 ODE2))" by auto
    ultimately show "{z. swap x y z \<in> ODE_vars I (OProd ODE1 ODE2)} = ODE_vars I (OUrename x y (OProd ODE1 ODE2))"
      by blast
  qed
  done

lemma ren_proj:"(RSadj x y a) $ z = a $ (swap x y z)"
  unfolding RSadj_def by simp

lemma swap_cancel:"swap x y (swap x y z) = z"
  by auto

lemma mkv_lemma:
  assumes ORA:"ORadmit ODE"
  shows "Radj x y (mk_v I (OUrename x y ODE) (a, b) c) = mk_v I ODE (RSadj x y a, RSadj x y b) (RSadj x y c)"
proof -
  have inner1:"(mk_v I (OUrename x y ODE) (a, b) c) = ((\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then c else a) $ i), (\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then ODE_sem I (OUrename x y ODE) c else b) $ i))"
    using mk_v_concrete[of I "OUrename x y ODE" "(a,b)" c] by auto
  have inner2:"(((\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then c else a) $ i), (\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then ODE_sem I (OUrename x y ODE) c else b) $ i))) 
            = (((\<chi> i. (if (swap x y i) \<in> ODE_vars I ODE then c else a) $ i), (\<chi> i. (if (swap x y i) \<in> ODE_vars I ODE then ODE_sem I (OUrename x y ODE) c else b) $ i)))"
    by (force simp: OUrename_preserves_ODE_vars[OF ORA, symmetric])
  have "Radj x y (mk_v I (OUrename x y ODE) (a, b) c) = 
        Radj x y (((\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then c else a) $ i), (\<chi> i. (if i \<in> ODE_vars I (OUrename x y ODE) then ODE_sem I (OUrename x y ODE) c else b) $ i)))"
    using inner1 by auto
  moreover have "... = Radj x y (((\<chi> i. (if (swap x y i) \<in> ODE_vars I ODE then c else a) $ i), 
                              (\<chi> i. (if (swap x y i) \<in> ODE_vars I ODE then ODE_sem I (OUrename x y ODE) c else b) $ i)))"
    using inner2 by auto
  moreover have "... = (((\<chi> i. (if (swap x y (swap x y i)) \<in> ODE_vars I ODE then c else a) $ (swap x y i))),
                         (\<chi> i. (if (swap x y (swap x y i)) \<in> ODE_vars I ODE then ODE_sem I (OUrename x y ODE) c else b) $ (swap x y i)))"
    unfolding Radj_def RSadj_def by auto
  moreover have "... = (((\<chi> i. (if i \<in> ODE_vars I ODE then c else a) $ (swap x y i))),
                         (\<chi> i. (if i \<in> ODE_vars I ODE then ODE_sem I (OUrename x y ODE) c else b) $ (swap x y i)))"
    using swap_cancel by auto
  moreover have "... = (((\<chi> i. (if i \<in> ODE_vars I ODE then RSadj x y c else RSadj x y a) $ i)),
                         (\<chi> i. (if i \<in> ODE_vars I ODE then RSadj x y (ODE_sem I (OUrename x y ODE) c) else RSadj x y b) $ i))"
     by(auto simp add: ren_proj)
  moreover have "... = (((\<chi> i. (if i \<in> ODE_vars I ODE then RSadj x y c else RSadj x y a) $ i)),
                         (\<chi> i. (if i \<in> ODE_vars I ODE then RSadj x y (RSadj x y (ODE_sem I ODE (RSadj x y c))) else RSadj x y b) $ i))"
    using OUren[OF ORA, of I x y c] by auto
  moreover have "... = (((\<chi> i. (if i \<in> ODE_vars I ODE then RSadj x y c else RSadj x y a) $ i)),
                         (\<chi> i. (if i \<in> ODE_vars I ODE then (ODE_sem I ODE (RSadj x y c)) else RSadj x y b) $ i))"
    by(auto simp add: RSadj_cancel)
  moreover have "... = mk_v I ODE (RSadj x y a, RSadj x y b) (RSadj x y c)"
    using mk_v_concrete[of I "ODE" "(RSadj x y a, RSadj x y b)" "RSadj x y c"]
    by auto
  ultimately show ?thesis by auto
qed

lemma sol_lemma:
  assumes ORA:"ORadmit ODE"
  assumes t:"0 \<le> t"
  assumes fml:"\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>)"
  assumes sol:"(sol solves_ode (\<lambda>a. ODE_sem I (OUrename x y ODE))) {0..t} {xa. mk_v I (OUrename x y ODE) (sol 0, b) xa \<in> fml_sem I (FUrename x y \<phi>)}"
  shows "((\<lambda>t. RSadj x y (sol t)) solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {xa. mk_v I ODE (RSadj x y (sol 0), RSadj x y b) xa \<in> fml_sem I \<phi>}"
  apply(unfold solves_ode_def)
  apply(rule conjI)
   defer
   subgoal 
     apply auto
   proof -
     fix s
     assume t:"0 \<le> s" "s \<le> t"
     have ivl:"s \<in> {0..t}" using t by auto
     have "mk_v I (OUrename x y ODE) (sol 0,b) (sol s) \<in> fml_sem I (FUrename x y \<phi>)"
       using solves_odeD(2)[OF sol ivl] by auto
     then have "Radj x y (mk_v I (OUrename x y ODE) (sol 0, b) (sol s)) \<in> fml_sem I \<phi>"
       using fml[of "mk_v I (OUrename x y ODE) (sol 0, b) (sol s)"] by auto
     then show "mk_v I ODE (RSadj x y (sol 0), RSadj x y b) (RSadj x y (sol s)) \<in> fml_sem I \<phi>"
         using mkv_lemma[OF ORA, of x y I "sol 0" b "sol s"] by auto
   qed
   apply (unfold has_vderiv_on_def has_vector_derivative_def)
   proof -
     have "\<And>s. s\<in>{0..t} \<Longrightarrow>  ((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I ODE (RSadj x y (sol s)))) (at s within {0..t})"
     proof -
       fix s
       assume s:"s \<in>{0..t}"
       let ?g = "RSadj x y"
       let ?g' = "RSadj x y"
       let ?f = "sol"
       let ?f' = "(\<lambda>t'. t' *\<^sub>R ODE_sem I (OUrename x y ODE) (sol s))"
       let ?h = "?g \<circ> ?f"
       
       have fun_eq:"(\<lambda>t'. t' *\<^sub>R ODE_sem I (OUrename x y ODE) (sol s)) = (\<lambda>t'. t' *\<^sub>R (RSadj x y (ODE_sem I ODE (RSadj x y (sol s)))))"
         apply(rule ext)
         using OUren[OF ORA, of I x y] by simp
       have fun_eq1:"(\<lambda>\<nu>. (\<chi> i. RSadj x y \<nu> $ i)) = RSadj x y"
         by(rule ext, rule vec_extensionality, simp)
       have "s \<in> {0..t} \<Longrightarrow> (sol has_derivative (\<lambda>t'. t' *\<^sub>R ODE_sem I (OUrename x y ODE) (sol s))) (at s within {0..t})"
         using solves_odeD(1)[OF sol] unfolding has_vderiv_on_def has_vector_derivative_def by auto
       then have fderiv:"s \<in> {0..t} \<Longrightarrow> (?f has_derivative ?f') (at s within {0..t})"
         using fun_eq by auto
       have "((\<lambda>\<nu>. (\<chi> i. RSadj x y \<nu> $ i)) has_derivative (\<lambda>\<nu>'. (\<chi> i . RSadj x y \<nu>' $ i))) (at (?f s) within ?f ` {0..t})"
         apply(rule has_derivative_vec)
         apply(auto simp add: RSadj_def intro:derivative_eq_intros)
           by (simp add: has_derivative_at_withinI has_derivative_proj')+
       then have gderiv:"(RSadj x y has_derivative (RSadj x y)) (at (?f s) within ?f ` {0..t})"
         using fun_eq1 by auto
       have hderiv:"(?h has_derivative (?g' \<circ> ?f')) (at s within {0..t})"
         by (rule diff_chain_within[OF fderiv gderiv], rule s)
       have heq:"(\<lambda>t. RSadj x y (sol t)) = ?h"
         unfolding comp_def by simp
       have RSadj_scale:"\<And>c a. RSadj x y (c *\<^sub>R RSadj x y a) = c *\<^sub>R a"
         subgoal for c a
           unfolding RSadj_def
           apply auto
           apply(rule vec_extensionality)
           by(auto)
         done
       have heq':"(\<lambda>xb. xb *\<^sub>R ODE_sem I ODE (RSadj x y (sol s))) = (?g' \<circ> ?f')"
         unfolding comp_def apply(rule ext) using OUren[OF ORA, of I x y "sol s"]
         apply auto
         subgoal for c
           using RSadj_scale[of c "ODE_sem I ODE (RSadj x y (sol s))"] by auto            
         done
       show "((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I ODE (RSadj x y (sol s)))) (at s within {0..t})"
         using heq heq' hderiv by auto 
       qed
    then show "\<forall>xa\<in>{0..t}. ((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I ODE (RSadj x y (sol xa)))) (at xa within {0..t})"
      by auto
    qed

lemma sol_lemma2:
  assumes ORA:"ORadmit ODE"
  assumes t:"0 \<le> t"
  assumes fml:"\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>)"
  assumes sol:"(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I \<phi>}"
  shows "((\<lambda>t. RSadj x y (sol t)) solves_ode (\<lambda>a. ODE_sem I (OUrename x y ODE))) {0..t} 
          {xa. mk_v I (OUrename x y ODE) (RSadj x y (sol 0), RSadj x y b) xa \<in> fml_sem I (FUrename x y \<phi>)}"
  apply(unfold solves_ode_def)
  apply(rule conjI)
   defer
   subgoal 
     apply auto
   proof -
     fix s
     assume t:"0 \<le> s" "s \<le> t"
     have ivl:"s \<in> {0..t}" using t by auto
     have "mk_v I ODE (sol 0,b) (sol s) \<in> fml_sem I \<phi>"
       using solves_odeD(2)[OF sol ivl] by auto
     then have "Radj x y (mk_v I ODE (sol 0, b) (sol s)) \<in> fml_sem I (FUrename x y \<phi>)"
       using Radj_cancel[of x y "(mk_v I ODE (sol 0, b) (sol s))"]
       by (simp add: fml)
     then show " mk_v I (OUrename x y ODE) (RSadj x y (sol 0), RSadj x y b) (RSadj x y (sol s)) \<in> fml_sem I (FUrename x y \<phi>)"
         using mkv_lemma[OF ORA, of x y I "RSadj x y (sol 0)" "RSadj x y b" "RSadj x y (sol s)"]
         by (simp add: RSadj_cancel \<open>mk_v I ODE (sol 0, b) (sol s) \<in> fml_sem I \<phi>\<close> fml)
   qed
   apply (unfold has_vderiv_on_def has_vector_derivative_def)
 proof -
   have "\<And>s. s\<in>{0..t} \<Longrightarrow>  ((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I (OUrename x y ODE) (RSadj x y (sol s)))) (at s within {0..t})"
   proof -
     fix s
     assume s:"s \<in>{0..t}"
     let ?g = "RSadj x y"
     let ?g' = "RSadj x y"
     let ?f = "sol"
     let ?f' = "(\<lambda>xb. xb *\<^sub>R RSadj x y (ODE_sem I (OUrename x y ODE) (RSadj x y (sol s))))"
     let ?h = "?g \<circ> ?f"
     have fun_eq:"(\<lambda>t'. t' *\<^sub>R ODE_sem I ODE (sol s)) = (\<lambda>xb. xb *\<^sub>R RSadj x y (ODE_sem I (OUrename x y ODE) (RSadj x y (sol s))))"
       apply(rule ext)
       using OUren[OF ORA, of I x y, of "RSadj x y (sol s)"] RSadj_cancel by simp
     have fun_eq1:"(\<lambda>\<nu>. (\<chi> i. RSadj x y \<nu> $ i)) = RSadj x y"
       by(rule ext, rule vec_extensionality, simp)
     have "s \<in> {0..t} \<Longrightarrow> (sol has_derivative (\<lambda>t'. t' *\<^sub>R ODE_sem I ODE (sol s))) (at s within {0..t})"
       using solves_odeD(1)[OF sol] unfolding has_vderiv_on_def has_vector_derivative_def by auto
     then have fderiv:"s \<in> {0..t} \<Longrightarrow> (?f has_derivative ?f') (at s within {0..t})"
       using fun_eq by auto
     have "((\<lambda>\<nu>. (\<chi> i. RSadj x y \<nu> $ i)) has_derivative (\<lambda>\<nu>'. (\<chi> i . RSadj x y \<nu>' $ i))) (at (?f s) within ?f ` {0..t})"
       apply(rule has_derivative_vec)
       apply(auto simp add: RSadj_def intro:derivative_eq_intros)
         by (simp add: has_derivative_at_withinI has_derivative_proj')+
     then have gderiv:"(RSadj x y has_derivative (RSadj x y)) (at (?f s) within ?f ` {0..t})"
       using fun_eq1 by auto
     have hderiv:"(?h has_derivative (?g' \<circ> ?f')) (at s within {0..t})"
       by (rule diff_chain_within[OF fderiv gderiv], rule s)
     have heq:"(\<lambda>t. RSadj x y (sol t)) = ?h"
       unfolding comp_def by simp
     have RSadj_scale:"\<And>c a. RSadj x y (c *\<^sub>R RSadj x y a) = c *\<^sub>R a"
       subgoal for c a
         unfolding RSadj_def
         apply auto
         apply(rule vec_extensionality)
         by(auto)
       done
     have heq':"(\<lambda>xb. xb *\<^sub>R ODE_sem I (OUrename x y ODE) (RSadj x y (sol s))) = (?g' \<circ> ?f')"
       unfolding comp_def apply(rule ext) using OUren[OF ORA, of I x y "RSadj x y (sol s)"]
       apply auto
       subgoal for c
         using RSadj_scale[of c "ODE_sem I (OUrename x y ODE) (RSadj x y (sol s))"] RSadj_cancel[of x y "sol s"]
             RSadj_cancel[of x y "ODE_sem I ODE (sol s)"] by auto
       done
     show "((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I (OUrename x y ODE) (RSadj x y (sol s)))) (at s within {0..t})"
       using heq heq' hderiv by auto 
       qed
  then show "\<forall>xa\<in>{0..t}. ((\<lambda>t. RSadj x y (sol t)) has_derivative (\<lambda>xb. xb *\<^sub>R ODE_sem I (OUrename x y ODE) (RSadj x y (sol xa)))) (at xa within {0..t})"
  by blast
qed
    
lemma PUren_FUren:
  assumes good_interp:"is_interp I"
  shows
    "(PRadmit \<alpha> \<longrightarrow> hpsafe \<alpha> \<longrightarrow> (\<forall> \<nu> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PUrename x y \<alpha>) \<longleftrightarrow> (Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I \<alpha>))
    \<and> (FRadmit \<phi> \<longrightarrow> fsafe \<phi> \<longrightarrow> (\<forall> \<nu>. \<nu> \<in> fml_sem I (FUrename x y \<phi>) \<longleftrightarrow> (Radj x y \<nu>) \<in> fml_sem I \<phi>))"
proof(induction rule: PRadmit_FRadmit.induct)
  case (FRadmit_Geq \<theta>1 \<theta>2)
  then show ?case using TUren[OF good_interp] by auto
next
  case (FRadmit_Exists \<phi> z) then have
    FRA:"FRadmit \<phi>"
    and IH:"fsafe \<phi> \<Longrightarrow>  (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
    by auto
  have "fsafe (Exists z \<phi>) \<Longrightarrow>  (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>)))"
    apply (cases "z = x")
     subgoal for \<nu>
     proof -
       assume fsafe:"fsafe (Exists z \<phi>)"
       assume zx:"z = x"
       from fsafe have fsafe':"fsafe \<phi>" by auto
       have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
         by (rule IH[OF fsafe'])
       have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists y (FUrename x y \<phi>)))" using zx by auto
       moreover have "... = (\<exists>r. (repv \<nu> y r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
       moreover have "... = (\<exists>r. (Radj x y (repv \<nu> y r)) \<in> fml_sem I \<phi>)" using IH' by auto
       moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) x r) \<in> fml_sem I \<phi>)" using Radj_repv1[of x y \<nu>] by auto
       moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
       ultimately 
       show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
         by auto
     qed
    apply (cases "z = y")
     subgoal for \<nu>
     proof -
       assume fsafe:"fsafe (Exists z \<phi>)"
       assume zx:"z = y"
       from fsafe have fsafe':"fsafe \<phi>" by auto
       have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
         by (rule IH[OF fsafe'])
       have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists x (FUrename x y \<phi>)))" using zx by auto
       moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
       moreover have "... = (\<exists>r. (Radj x y (repv \<nu> x r)) \<in> fml_sem I \<phi>)" using IH' by auto
       moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) y r) \<in> fml_sem I \<phi>)" using Radj_repv2[of x y \<nu>] by auto
       moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
       ultimately 
       show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
         by auto
     qed
    subgoal for \<nu>
    proof -
      assume fsafe:"fsafe (Exists z \<phi>)"
      assume zx:"z \<noteq> x" and zy:"z \<noteq> y"
      from fsafe have fsafe':"fsafe \<phi>" by auto
      have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
        by (rule IH[OF fsafe'])
      have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists z (FUrename x y \<phi>)))" using zx zy by auto
      moreover have "... = (\<exists>r. (repv \<nu> z r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
      moreover have "... = (\<exists>r. (Radj x y (repv \<nu> z r)) \<in> fml_sem I \<phi>)" using IH' by auto
      moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) z r) \<in> fml_sem I \<phi>)" using Radj_repv3[of z x y \<nu>, OF zx zy] by auto
      moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
      ultimately 
      show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
        by auto
    qed
    done
  then show ?case by auto 
next
  case (PRadmit_Assign z \<theta>)
  have "hpsafe (Assign z \<theta>) \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>)  \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (Assign z \<theta>)))"
    apply (cases "z = x")
     subgoal for \<nu> \<omega>
     proof -
       assume fsafe:"hpsafe (Assign z \<theta>)"
       assume zx:"z = x"
       from fsafe have dsafe:"dsafe \<theta>" by auto
       have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
         subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
       have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign y (TUrename x y \<theta>)))"  using zx by auto
       moreover have "... = (\<omega> = repv \<nu> y (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
       moreover have "... = (\<omega> = repv \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
       moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
       moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) x (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv1 by auto
       moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zx by auto
       moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
       ultimately 
       show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
         by auto
     qed
    apply (cases "z = y")
     subgoal for \<nu> \<omega>
     proof -
       assume fsafe:"hpsafe (Assign z \<theta>)"
       assume zy:"z = y"
       from fsafe have dsafe:"dsafe \<theta>" by auto
       have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
         subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
       have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign x (TUrename x y \<theta>)))"  using zy by auto
       moreover have "... = (\<omega> = repv \<nu> x (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
       moreover have "... = (\<omega> = repv \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
       moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
       moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) y (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv2 by auto
       moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zy by auto
       moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
       ultimately 
       show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
         by auto
     qed
    subgoal for \<nu> \<omega>
    proof -
      assume fsafe:"hpsafe (Assign z \<theta>)"
      assume zx:"z \<noteq> x" and zy:"z \<noteq> y"
      from fsafe have dsafe:"dsafe \<theta>" by auto
      have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
        subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
      have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign z (TUrename x y \<theta>)))"  using zx zy by auto
      moreover have "... = (\<omega> = repv \<nu> z (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
      moreover have "... = (\<omega> = repv \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
      moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
      moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv3[OF zx zy] by auto
      moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
      ultimately 
      show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
        by auto
    qed
    done
  then show ?case by auto
next
  case (PRadmit_DiffAssign z \<theta>)
  have "hpsafe (DiffAssign z \<theta>) \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>)  \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (DiffAssign z \<theta>)))"
    apply (cases "z = x")
     subgoal for \<nu> \<omega>
     proof -
       assume fsafe:"hpsafe (DiffAssign z \<theta>)"
       assume zx:"z = x"
       from fsafe have dsafe:"dsafe \<theta>" by auto
       have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
         subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
       have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (DiffAssign y (TUrename x y \<theta>)))"  using zx by auto
       moreover have "... = (\<omega> = repd \<nu> y (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
       moreover have "... = (\<omega> = repd \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
       moreover have "... = (Radj x y \<omega> = Radj x y (repd \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
       moreover have "... = (Radj x y \<omega> = repd (Radj x y \<nu>) x (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repd1 by auto
       moreover have "... = (Radj x y \<omega> = repd (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zx by auto
       moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))" by auto        
       ultimately 
       show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))"
         by auto
     qed
    apply (cases "z = y")
     subgoal for \<nu> \<omega>
     proof -
       assume fsafe:"hpsafe (DiffAssign z \<theta>)"
       assume zy:"z = y"
       from fsafe have dsafe:"dsafe \<theta>" by auto
       have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
         subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
       have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (DiffAssign x (TUrename x y \<theta>)))"  using zy by auto
       moreover have "... = (\<omega> = repd \<nu> x (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
       moreover have "... = (\<omega> = repd \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
       moreover have "... = (Radj x y \<omega> = Radj x y (repd \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
       moreover have "... = (Radj x y \<omega> = repd (Radj x y \<nu>) y (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repd2 by auto
       moreover have "... = (Radj x y \<omega> = repd (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zy by auto
       moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))" by auto        
       ultimately 
        show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))"
         by auto
     qed
    subgoal for \<nu> \<omega>
  proof -
    assume fsafe:"hpsafe (DiffAssign z \<theta>)"
    assume zx:"z \<noteq> x" and zy:"z \<noteq> y"
    from fsafe have dsafe:"dsafe \<theta>" by auto
    have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
      subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
    have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (DiffAssign z (TUrename x y \<theta>)))"  using zx zy by auto
    moreover have "... = (\<omega> = repd \<nu> z (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
    moreover have "... = (\<omega> = repd \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
    moreover have "... = (Radj x y \<omega> = Radj x y (repd \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
    moreover have "... = (Radj x y \<omega> = repd (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repd3[OF zx zy] by auto
    moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))" by auto        
    ultimately 
    show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (DiffAssign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (DiffAssign z \<theta>))"
      by auto
  qed
  done
  then show ?case by auto
next
  case (PRadmit_Test \<phi>) then
  have FRA:"FRadmit \<phi>"
  and IH:"fsafe \<phi> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
    by auto
  have "hpsafe (? \<phi>) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (? \<phi>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (? \<phi>)))"
    proof -
      assume hpsafe:"hpsafe (? \<phi>)"
      fix \<nu> \<omega>
      from hpsafe have fsafe:"fsafe \<phi>" by auto
      have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>)" 
        by (rule IH[OF fsafe])
      have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (? \<phi>))) = (\<nu> = \<omega> \<and> (\<omega> \<in> fml_sem I (FUrename x y \<phi>)))" by (cases \<omega>, auto)
      moreover have "... = (\<nu> = \<omega> \<and> (Radj x y \<omega>) \<in> fml_sem I \<phi>)" using IH' by auto
      moreover have "... = (Radj x y \<nu> = Radj x y \<omega> \<and> (Radj x y \<omega>) \<in> fml_sem I \<phi>)" using Radj_eq_iff by auto
      moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (? \<phi>))" by (cases "Radj x y \<omega>", auto)
      ultimately show "?thesis \<nu> \<omega>" by auto
    qed
  then show ?case by auto
next
  case (FRadmit_Prop p args) then
  have "fsafe (Prop p args) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y (Prop p args))) = ((Radj x y \<nu>) \<in> fml_sem I (Prop p args)))"
  proof -
    assume fsafe:"fsafe (Prop p args)"
    fix \<nu>
    from fsafe have dsafes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    have IH:"\<And>i \<nu>. dterm_sem I (TUrename x y (args i)) \<nu> = dterm_sem I (args i) (Radj x y \<nu>)"
      using TUren[OF good_interp dsafes] by auto
    have "(\<nu> \<in> fml_sem I (FUrename x y (Prop p args))) = (\<nu> \<in> fml_sem I (Prop p (\<lambda>i . TUrename x y (args i))))" by auto
    moreover have "... = (Predicates I p (\<chi> i. dterm_sem I (TUrename x y (args i)) \<nu>))" by auto
    moreover have "... = (Predicates I p (\<chi> i. dterm_sem I (args i) (Radj x y \<nu>)))" using IH by auto
    moreover have "... = ((Radj x y \<nu>) \<in> fml_sem I (Prop p args))" by auto
    ultimately show "?thesis \<nu>" by blast
  qed 
  then show ?case by auto
next
  case (PRadmit_Sequence a b) then 
  have IH1:"hpsafe a \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a))"
    and  IH2:"hpsafe b \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y b)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I b))"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (a ;;b))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    fix \<nu> \<omega>
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by auto
    have IH1:"(\<And>\<mu>. ((\<nu>, \<mu>) \<in> prog_sem I (PUrename x y a)) = ((Radj x y \<nu>, Radj x y \<mu>) \<in> prog_sem I a))"
      using IH1[OF safe1] by auto
    have IH2:"(\<And>\<mu>. ((\<mu>, \<omega>) \<in> prog_sem I (PUrename x y b)) = ((Radj x y \<mu>, Radj x y \<omega>) \<in> prog_sem I b))"
      using IH2[OF safe2] by auto
    have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (a ;;b))) = ((\<nu>, \<omega>) \<in> prog_sem I ((PUrename x y a) ;;(PUrename x y b)))" by auto
    moreover have "... = (\<exists>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PUrename x y a) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PUrename x y b))" by auto
    moreover have "... = (\<exists>\<mu>. (Radj x y \<nu>, Radj x y \<mu>) \<in> prog_sem I a \<and> (Radj x y \<mu>, Radj x y \<omega>) \<in> prog_sem I b)" using IH1 IH2 by auto
    moreover have "... = (\<exists>\<mu>. (Radj x y \<nu>, \<mu>) \<in> prog_sem I a \<and> (\<mu>, Radj x y \<omega>) \<in> prog_sem I b)" 
      apply auto
       subgoal for aa ba
         apply(rule exI[where x="fst(Radj x y (aa,ba))"])
         apply(rule exI[where x="snd(Radj x y (aa,ba))"])
         by auto
      subgoal for aa ba
        apply(rule exI[where x="fst(Radj x y (aa,ba))"])
        apply(rule exI[where x="snd(Radj x y (aa,ba))"])
        using Radj_cancel by auto
      done
    moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (a ;;b))" by (auto,blast)
    ultimately show "?thesis \<nu> \<omega>" by auto
  qed
  then show ?case by auto
next
  case (FRadmit_Diamond \<alpha> \<phi>) then
  have IH1:"hpsafe \<alpha> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y \<alpha>)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I \<alpha>))"
  and IH2:"fsafe \<phi> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
    by auto
  have "fsafe (\<langle>\<alpha>\<rangle>\<phi>) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y (\<langle>\<alpha>\<rangle>\<phi>))) = (Radj x y \<nu> \<in> fml_sem I (\<langle>\<alpha>\<rangle>\<phi>)))"
  proof -
    assume safe:"fsafe (\<langle>\<alpha>\<rangle>\<phi>)"
    fix \<nu>
    from safe have safe1:"hpsafe \<alpha>" and safe2:"fsafe \<phi>" by auto
    have IH1:"\<And>\<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y \<alpha>)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I \<alpha>)"
      using IH1[OF safe1] by auto
    have IH2:"\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>)"
      by (rule IH2[OF safe2])
    have "(\<nu> \<in> fml_sem I (FUrename x y (\<langle>\<alpha>\<rangle>\<phi>))) = (\<nu> \<in> fml_sem I (\<langle>PUrename x y \<alpha>\<rangle>FUrename x y \<phi>))" by auto
    moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PUrename x y \<alpha>) \<and> \<omega> \<in> fml_sem I (FUrename x y \<phi>))" by auto
    moreover have "... = (\<exists> \<omega>. (Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I \<alpha> \<and> (Radj x y \<omega>) \<in> fml_sem I \<phi>)" 
      using IH1 IH2 by auto
    moreover have "... = (\<exists> \<omega>. (Radj x y \<nu>, \<omega>) \<in> prog_sem I \<alpha> \<and> \<omega> \<in> fml_sem I \<phi>)"
      apply auto
       subgoal for aa ba
         apply(rule exI[where x="fst(Radj x y (aa,ba))"])
         apply(rule exI[where x="snd(Radj x y (aa,ba))"])
         by auto
      subgoal for aa ba
        apply(rule exI[where x="fst(Radj x y (aa,ba))"])
        apply(rule exI[where x="snd(Radj x y (aa,ba))"])
        using Radj_cancel by auto
      done
    moreover have "... = (Radj x y \<nu> \<in> fml_sem I (\<langle>\<alpha>\<rangle>\<phi>))" by auto
    ultimately show "?thesis \<nu>" by auto
  qed
  then show ?case by auto
next
  case (PRadmit_Loop a) then
  have IH:" hpsafe a \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a))"
    by auto
  have "hpsafe (a** ) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (a** ))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (a** )))"
  proof -
    assume safe:"hpsafe (a** )"
    fix \<nu> \<omega>
    from safe have safe:"hpsafe a" by auto
    have IH1:"(\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a)) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a))"
      by (rule IH[OF safe])
    have relpow_iff:"\<And>\<nu> \<omega> R n. ((\<nu>, \<omega>) \<in> R ^^ Suc n) = (\<exists>\<mu>. (\<nu>, \<mu>) \<in> R \<and> (\<mu>, \<omega>) \<in> R ^^ n)"
      apply auto
       subgoal for R n x y z by (auto simp add: relpow_Suc_D2')
      subgoal for \<nu> \<omega> R n \<mu> using relpow_Suc_I2 by fastforce
      done
    have rtrancl_iff_relpow:"\<And>\<nu> \<omega> R. ((\<nu>, \<omega>) \<in> R\<^sup>*) = (\<exists>n. (\<nu>, \<omega>) \<in> R ^^ n)"
      using rtrancl_imp_relpow relpow_imp_rtrancl by blast
    have lem:"\<And>n. (\<forall> \<nu> \<omega>.  ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a)^^n) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a^^n))"
      subgoal for n
      proof(induction n)
        case 0
        then show ?case using Radj_eq_iff by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a) ^^ n) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a ^^ n)"
          by auto
        have "\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a) ^^ Suc n) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a ^^ Suc n)"
        proof -
          fix \<nu> \<omega>
          have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y a) ^^ Suc n) 
            = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PUrename x y a) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PUrename x y a) ^^ n)"
            using relpow_iff[of \<nu> \<omega> n "prog_sem I (PUrename x y a)"] by auto
          moreover have "... = (\<exists> \<mu>. (Radj x y \<nu>, Radj x y \<mu>) \<in> prog_sem I a \<and> (Radj x y \<mu>, Radj x y \<omega>) \<in> prog_sem I a ^^ n)"
            using IH1 IH2 by blast
          moreover have "... = (\<exists> \<mu>. (Radj x y \<nu>, \<mu>) \<in> prog_sem I a \<and> (\<mu>, Radj x y \<omega>) \<in> prog_sem I a ^^ n)"
            apply auto
             subgoal for aa ba
               apply(rule exI[where x="fst(Radj x y (aa,ba))"])
               apply(rule exI[where x="snd(Radj x y (aa,ba))"])
               by auto
            subgoal for aa ba
              apply(rule exI[where x="fst(Radj x y (aa,ba))"])
              apply(rule exI[where x="snd(Radj x y (aa,ba))"])
              using Radj_cancel by auto
            done
          moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I a ^^ Suc n)"
            using relpow_iff[of "Radj x y \<nu>" "Radj x y \<omega>"  n "prog_sem I a"] by auto
          ultimately show "?thesis \<nu> \<omega>" by auto 
        qed
        then show ?case by auto
      qed
      done
    have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (a** ))) = ((\<nu>, \<omega>) \<in> (prog_sem I (PUrename x y a))\<^sup>*)" by auto
    moreover have "... = (\<exists>n. (\<nu>, \<omega>) \<in> (prog_sem I (PUrename x y a)) ^^ n)"
      using rtrancl_iff_relpow[of \<nu> \<omega> "prog_sem I (PUrename x y a)"] by auto
    moreover have "... = (\<exists>n. (Radj x y \<nu>, Radj x y \<omega>) \<in> (prog_sem I a) ^^ n)"
      using lem by blast
    moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> (prog_sem I a)\<^sup>*)"
      using rtrancl_iff_relpow[of "Radj x y \<nu>" "Radj x y \<omega>" "prog_sem I a"] by auto
    moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (a** ))" by auto
    ultimately show "?thesis \<nu> \<omega>" by blast
  qed
  then show ?case by auto
next
  case (PRadmit_EvolveODE ODE \<phi>) then
  have ORA:"ORadmit ODE"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
    by auto
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (EvolveODE ODE \<phi>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (EvolveODE ODE \<phi>)))"
  proof -
    assume safe:"hpsafe (EvolveODE ODE \<phi>)"
    fix \<nu> \<omega>
    from safe have osafe:"osafe ODE" and fsafe:"fsafe \<phi>" by auto
    have IH1:"\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>) = (Radj x y \<nu> \<in> fml_sem I \<phi>))" by (rule IH[OF fsafe])
    have IH2:"\<And>\<nu>. ODE_sem I (OUrename x y ODE) \<nu> = RSadj x y (ODE_sem I ODE (RSadj x y \<nu>))"
      using OUren[OF ORA] by auto
    have RSadj_Radj:"\<And>a b. (RSadj x y a, RSadj x y b) = Radj x y (a,b)"
      unfolding RSadj_def Radj_def by auto
    have Radj_swap:"\<And>a b. Radj x y a = b \<Longrightarrow> a = Radj x y b"
      using Radj_cancel Radj_eq_iff by metis
    have mkv:"\<And>t sol b. Radj x y (mk_v I (OUrename x y ODE) (sol 0, b) (sol t)) = mk_v I ODE (RSadj x y (sol 0), RSadj x y b) (RSadj x y (sol t))"
      using mkv_lemma[OF ORA] by blast
    have mkv2:"\<And>t sol b.  Radj x y \<omega> = mk_v I ODE (sol 0, b) (sol t) \<Longrightarrow>
      \<omega> = mk_v I (OUrename x y ODE) (RSadj x y (sol 0), RSadj x y b) (RSadj x y (sol t))"
      using mkv_lemma[OF ORA] by (metis RSadj_cancel Radj_cancel)
    have sol:"\<And>t sol b. 0 \<le> t \<Longrightarrow>
      (sol solves_ode (\<lambda>a. ODE_sem I (OUrename x y ODE))) {0..t} {xa. mk_v I (OUrename x y ODE) (sol 0, b) xa \<in> fml_sem I (FUrename x y \<phi>)} \<Longrightarrow>
      ((\<lambda>t. RSadj x y (sol t)) solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {xa. mk_v I ODE (RSadj x y (sol 0), RSadj x y b) xa \<in> fml_sem I \<phi>}"
      using sol_lemma IH1 IH2 ORA by blast
    have sol2:"\<And>t sol b. 0 \<le> t \<Longrightarrow>
(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I \<phi>} \<Longrightarrow>
((\<lambda>t. RSadj x y (sol t)) solves_ode (\<lambda>a. ODE_sem I (OUrename x y ODE))) {0..t}
 {xa. mk_v I (OUrename x y ODE) (RSadj x y (sol 0), RSadj x y b) xa \<in> fml_sem I (FUrename x y \<phi>)}"
      using sol_lemma2 IH1 IH2 ORA by blast
    show "?thesis \<nu> \<omega>"
      apply auto
       subgoal for b sol t
         apply(rule exI[where x= "RSadj x y b"])
         apply(rule exI[where x= "(\<lambda>t. RSadj x y (sol t))"])
         apply(rule conjI)
          subgoal using RSadj_Radj[of "sol 0" "b"] by auto
         apply(rule exI[where x =t])
         apply(rule conjI)
          subgoal by (rule mkv)
         apply(rule conjI)
          subgoal by assumption
         by (rule sol)
      subgoal for b sol t
        apply(rule exI[where x= "RSadj x y b"])
        apply(rule exI[where x= "(\<lambda>t. RSadj x y (sol t))"])
        apply(rule conjI)
         subgoal using RSadj_Radj[of "sol 0" "b"] Radj_swap[of \<nu> "(sol 0,b)"] by auto
        apply(rule exI[where x =t])
        apply(rule conjI)
         subgoal by (rule mkv2)
        apply(rule conjI)
         subgoal by assumption
        by (rule sol2)
      done
    qed
  then show ?case by auto
qed (auto simp add: Radj_def)

lemma FUren:"is_interp I \<Longrightarrow> FRadmit \<phi> \<Longrightarrow> fsafe \<phi> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
  using PUren_FUren by blast

subsection \<open>Uniform Renaming Rule Soundness\<close>
lemma URename_sound:"FRadmit \<phi> \<Longrightarrow> fsafe \<phi> \<Longrightarrow> valid \<phi> \<Longrightarrow> valid (FUrename x y \<phi>)"
  unfolding valid_def using FUren by blast

subsection \<open>Bound Renaming Rule Soundness\<close>
lemma BRename_sound:
  assumes FRA:"FRadmit([[Assign x \<theta>]]\<phi>)"
  assumes fsafe:"fsafe ([[Assign x \<theta>]]\<phi>)"
  assumes valid:"valid ([[Assign x \<theta>]]\<phi>)"
  assumes FVF:"{Inl y, Inr y, Inr x} \<inter> FVF \<phi> = {}"
  shows "valid([[Assign y \<theta>]]FUrename x y \<phi>)"
proof -
  have FRA':"FRadmit \<phi>" using FRA 
    by (metis (no_types, lifting) Box_def FRadmit.cases formula.distinct(15) formula.distinct(21) formula.distinct(27) formula.distinct(29) formula.distinct(3) formula.distinct(31) formula.distinct formula.distinct(9) formula.inject(3) formula.inject(6))
  have fsafe':"fsafe \<phi>" using fsafe  by (simp add: Box_def)
  have dsafe:"dsafe \<theta>" using fsafe by (simp add: Box_def)
  have "\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I ([[y := \<theta>]]FUrename x y \<phi>)"
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good_interp:"is_interp I"
    from FVF have sub:"FVF \<phi> \<subseteq> -{Inl y, Inr y, Inr x}" by auto
    have "Vagree (repv (Radj x y \<nu>) x (dterm_sem I \<theta> \<nu>)) (repv \<nu> x (dterm_sem I \<theta> \<nu>)) (-{Inl y, Inr y, Inr x})"
      unfolding Vagree_def using FVF unfolding Radj_def RSadj_def by auto
    then have agree:"Vagree (repv (Radj x y \<nu>) x (dterm_sem I \<theta> \<nu>)) (repv \<nu> x (dterm_sem I \<theta> \<nu>)) (FVF \<phi>)"
      using agree_sub[OF sub] by auto
    have fml_sem_eq:"(repv (Radj x y \<nu>) x (dterm_sem I \<theta> \<nu>) \<in> fml_sem I \<phi>) = (repv \<nu> x (dterm_sem I \<theta> \<nu>) \<in> fml_sem I \<phi>)"
      using coincidence_formula[OF fsafe' Iagree_refl agree] by auto
    have "(\<nu> \<in> fml_sem I ([[y := \<theta>]]FUrename x y \<phi>)) = (repv \<nu> y (dterm_sem I \<theta> \<nu>) \<in> fml_sem I (FUrename x y \<phi>))"
      by auto
    moreover have "... = (Radj x y (repv \<nu> y (dterm_sem I \<theta> \<nu>)) \<in> fml_sem I \<phi>)"
      using FUren[OF good_interp FRA' fsafe'] by auto
    moreover have "... = (repv (Radj x y \<nu>) x (dterm_sem I \<theta> \<nu>) \<in> fml_sem I \<phi>)"
      using Radj_repv1 by auto
    moreover have "... = (\<nu> \<in> fml_sem I ([[x := \<theta>]]\<phi>))"
      using fml_sem_eq by auto
    moreover have "... = True"
      using valid unfolding valid_def using good_interp by blast
    ultimately
    show "\<nu> \<in> fml_sem I ([[y := \<theta>]]FUrename x y \<phi>)"
      by blast
  qed
  then
  show ?thesis unfolding valid_def by auto
qed
  


end end
