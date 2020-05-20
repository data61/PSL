subsection "Big step Semantics on partial states"

theory Big_StepT_Partial
imports Partial_Evaluation Big_StepT "SepLogAdd/Sep_Algebra_Add"  
    "HOL-Eisbach.Eisbach"
begin


type_synonym lvname = string 
type_synonym pstate_t = "partstate * nat"
type_synonym assnp = "partstate \<Rightarrow> bool"
type_synonym assn2 = "pstate_t \<Rightarrow> bool" 

subsubsection \<open>helper functions\<close>
     
paragraph \<open>restrict\<close>
    
definition restrict where "restrict S s = (%x. if x:S then Some (s x) else None)"
   
lemma restrictI: "\<forall>x\<in>S. s1 x = s2 x \<Longrightarrow> restrict S s1 = restrict S s2"
  unfolding restrict_def by fastforce
    
lemma restrictE: "restrict S s1 = restrict S s2 \<Longrightarrow> s1 = s2 on S"
  unfolding restrict_def by (meson option.inject)   
        
lemma dom_restrict[simp]: "dom (restrict S s) = S"
  unfolding restrict_def
  using domIff by fastforce
       
lemma restrict_less_part: "restrict S t \<preceq> part t"      
  unfolding restrict_def map_le_substate_conv[symmetric] map_le_def part_def apply auto 
  by (metis option.simps(3))
   
paragraph \<open>Heap helper functions\<close> 
        
fun lmaps_to_expr :: "aexp \<Rightarrow> val \<Rightarrow> assn2" where
  "lmaps_to_expr a v = (%(s,c). dom s = vars a \<and> paval a s = v \<and> c = 0)"
  
fun lmaps_to_expr_x :: "vname \<Rightarrow> aexp \<Rightarrow> val \<Rightarrow> assn2" where
  "lmaps_to_expr_x x a v = (%(s,c). dom s = vars a \<union> {x} \<and> paval a s = v \<and> c = 0)"
      
lemma subState: "x \<preceq> y \<Longrightarrow> v \<in> dom x \<Longrightarrow> x v = y v" unfolding map_le_substate_conv[symmetric] map_le_def  
  by blast 
       
lemma  fixes ps:: partstate
    and s::state
  assumes "vars a \<subseteq> dom ps" "ps \<preceq> part s"
  shows emb_update: "emb [x \<mapsto> paval a ps] s = (emb ps s) (x := aval a (emb ps s))"
    using assms
      unfolding emb_def apply auto apply (rule ext)
      apply(case_tac "v=x")
        apply(simp add: paval_aval)
      apply(simp) unfolding part_def apply(case_tac "v \<in> dom ps")
      using subState apply fastforce
      by (simp add: domIff)       
  
lemma paval_aval2: "vars a \<subseteq> dom ps \<Longrightarrow> ps \<preceq> part s \<Longrightarrow> paval a ps = aval a s"
  apply(induct a) using subState unfolding part_def apply auto  
  by fastforce  
    
lemma  fixes ps:: partstate
    and s::state
  assumes "vars a \<subseteq> dom ps" "ps \<preceq> part s"
  shows emb_update2: "emb (ps(x \<mapsto> paval a ps)) s = (emb ps s)(x := aval a (emb ps s))"
    using assms
      unfolding emb_def apply auto apply (rule ext)
      apply(case_tac "v=x")
        apply(simp add: paval_aval)
      by (simp)             
     
    
subsubsection "Big step Semantics on partial states"

inductive
  big_step_t_part :: "com \<times> partstate \<Rightarrow> nat \<Rightarrow> partstate \<Rightarrow> bool"  ("_ \<Rightarrow>\<^sub>A _ \<Down> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow>\<^sub>A Suc 0 \<Down> s" |
Assign: "\<lbrakk> vars a \<union> {x} \<subseteq> dom ps; paval a ps = v ; ps' = ps(x \<mapsto> v) \<rbrakk> \<Longrightarrow> (x ::= a,ps) \<Rightarrow>\<^sub>A Suc 0 \<Down> ps'" |

Seq: "\<lbrakk> (c1,s1) \<Rightarrow>\<^sub>A x \<Down> s2;  (c2,s2) \<Rightarrow>\<^sub>A y \<Down> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>A z \<Down> s3" |

IfTrue: "\<lbrakk> vars b \<subseteq> dom ps ; dom ps' = dom ps ; pbval b ps;  (c1,ps) \<Rightarrow>\<^sub>A x \<Down> ps'; y=x+1 \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, ps) \<Rightarrow>\<^sub>A y \<Down> ps'" |
IfFalse: "\<lbrakk> vars b \<subseteq> dom ps ; dom ps' = dom ps ; \<not> pbval b ps;  (c2,ps) \<Rightarrow>\<^sub>A x \<Down> ps'; y=x+1  \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, ps) \<Rightarrow>\<^sub>A y \<Down> ps'" |
WhileFalse: "\<lbrakk> vars b \<subseteq> dom s; \<not> pbval b s \<rbrakk> \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow>\<^sub>A Suc 0 \<Down> s" |
WhileTrue: "\<lbrakk> pbval b s1; vars b \<subseteq> dom s1;  (c,s1) \<Rightarrow>\<^sub>A x \<Down> s2;  (WHILE b DO c, s2) \<Rightarrow>\<^sub>A y \<Down> s3; 1+x+y=z  \<rbrakk> 
          \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow>\<^sub>A z \<Down> s3"


declare big_step_t_part.intros [intro]

    
inductive_cases Skip_tE3[elim!]: "(SKIP,s) \<Rightarrow>\<^sub>A x \<Down> t"
thm Skip_tE3 
inductive_cases Assign_tE3[elim!]: "(x ::= a,s) \<Rightarrow>\<^sub>A p \<Down> t"
thm Assign_tE3
inductive_cases Seq_tE3[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^sub>A p \<Down> s3"
thm Seq_tE3
inductive_cases If_tE3[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow>\<^sub>A x \<Down> t"
thm If_tE3
inductive_cases While_tE3[elim]: "(WHILE b DO c,s) \<Rightarrow>\<^sub>A x \<Down> t"
thm While_tE3

  
lemmas big_step_t_part_induct = big_step_t_part.induct[split_format(complete)]
  
  
lemma big_step_t3_post_dom_conv: "(c,ps) \<Rightarrow>\<^sub>A t \<Down> ps' \<Longrightarrow> dom ps' = dom ps"
apply(induct rule: big_step_t_part_induct) apply (auto simp: sep_disj_fun_def plus_fun_def)
  apply metis   done
      
lemma add_update_distrib: "ps1 x1 = Some y \<Longrightarrow> ps1 ## ps2 \<Longrightarrow> vars x2 \<subseteq> dom ps1 \<Longrightarrow> ps1(x1 \<mapsto> paval x2 ps1) + ps2  = (ps1 + ps2)(x1 \<mapsto> paval x2 ps1)"
  apply (rule ext)
  apply (auto simp: sep_disj_fun_def plus_fun_def)
  by (metis disjoint_iff_not_equal domI domain_conv)   
  
lemma paval_extend:  "ps1 ## ps2 \<Longrightarrow> vars a \<subseteq> dom ps1 \<Longrightarrow> paval a (ps1 + ps2) = paval a ps1" 
apply(induct a) apply (auto simp: sep_disj_fun_def domain_conv)
  by (metis domI map_add_comm map_add_dom_app_simps(1) option.sel plus_fun_conv) 
    
lemma pbval_extend: "ps1 ## ps2 \<Longrightarrow> vars b \<subseteq> dom ps1 \<Longrightarrow> pbval b (ps1 + ps2) = pbval b ps1" 
apply(induct b)  by (auto simp: paval_extend) 
     
    
lemma Framer: "(C, ps1) \<Rightarrow>\<^sub>A m \<Down> ps1' \<Longrightarrow> ps1 ## ps2 \<Longrightarrow> (C, ps1 + ps2) \<Rightarrow>\<^sub>A m \<Down>  ps1'+ps2"
proof (induct rule: big_step_t_part_induct)  
  case (Skip s)
  then show ?case by (auto simp: big_step_t_part.Skip)  
next
  case (Assign a x ps v ps')
  show ?case apply(rule big_step_t_part.Assign)  
    using Assign 
     apply (auto simp: plus_fun_def)  
    apply(rule ext)
    apply(case_tac "xa=x") 
    subgoal apply (auto simp: ) subgoal using paval_extend[unfolded plus_fun_def] by auto
       unfolding sep_disj_fun_def
       by (metis disjoint_iff_not_equal domI domain_conv) 
   subgoal by auto   
     done
next
  case (IfTrue b ps ps' c1 x y c2)
  then show ?case apply (auto ) apply(subst big_step_t_part.IfTrue)
         apply (auto simp: pbval_extend) 
      subgoal      by (auto simp: plus_fun_def)
      subgoal      by (auto simp: plus_fun_def)
      subgoal      by (auto simp: plus_fun_def) 
          done
next
  case (IfFalse b ps ps' c2 x y c1)
  then show ?case apply (auto ) apply(subst big_step_t_part.IfFalse)
         apply (auto simp: pbval_extend) 
      subgoal      by (auto simp: plus_fun_def)
      subgoal      by (auto simp: plus_fun_def)
      subgoal      by (auto simp: plus_fun_def) 
          done
next
  case (WhileFalse b s c)
  then show ?case apply(subst big_step_t_part.WhileFalse)
      subgoal      by (auto simp: plus_fun_def)
      subgoal      by (auto simp: pbval_extend)
          by auto
next
  case (WhileTrue b s1 c x s2 y s3 z)
  from big_step_t3_post_dom_conv[OF WhileTrue(3)]  have "dom s2 = dom s1" by auto
  with WhileTrue(8) have "s2 ## ps2" unfolding sep_disj_fun_def domain_conv by auto
  with WhileTrue show ?case apply auto apply(subst big_step_t_part.WhileTrue)
      subgoal      by (auto simp: pbval_extend)
      subgoal      by (auto simp: plus_fun_def)
             apply (auto) done
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  from big_step_t3_post_dom_conv[OF Seq(1)]  have "dom s2 = dom s1" by auto
  with Seq(6) have "s2 ## ps2" unfolding sep_disj_fun_def domain_conv by auto
  with Seq show ?case apply (subst big_step_t_part.Seq)
      by auto
qed
   
   
lemma Framer2: "(C, ps1) \<Rightarrow>\<^sub>A m \<Down> ps1' \<Longrightarrow> ps1 ## ps2 \<Longrightarrow> ps = ps1 + ps2 \<Longrightarrow> ps' = ps1'+ps2 \<Longrightarrow> (C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' "
  using Framer by auto
  
(* connection to bigstep2 *)
   
subsubsection \<open>Relation to BigStep Semantic on full states\<close> 
    
lemma paval_aval_part: "paval a (part s) = aval a s"
  apply(induct a) by (auto simp: part_def) 
lemma pbval_bval_part: "pbval b (part s) = bval b s"
  apply(induct b) by (auto simp: paval_aval_part) 
 
    
lemma part_paval_aval: "part (s(x := aval a s)) = part s(x \<mapsto> paval a (part s))"
  apply(rule ext)
  apply(case_tac "xa=x")  
    unfolding part_def apply auto by (metis (full_types) domIff map_le_def map_le_substate_conv option.distinct(1) part_def paval_aval2 subsetI) 
       
      
lemma full_to_part: "(C, s) \<Rightarrow> m \<Down> s' \<Longrightarrow>  (C, part s) \<Rightarrow>\<^sub>A m \<Down> part s' " 
apply(induct rule: big_step_t_induct)
  using Skip apply simp 
       apply (subst Assign)
          using part_paval_aval apply(simp_all add: )
    apply(rule Seq) apply auto
    apply(rule IfTrue) apply (auto simp: pbval_bval_part)
    apply(rule IfFalse) apply (auto simp: pbval_bval_part)
    apply(rule WhileFalse) apply (auto simp: pbval_bval_part)
  apply(rule WhileTrue) apply (auto simp: pbval_bval_part)
  done        
  
lemma part_to_full': "(C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<Longrightarrow> (C, emb ps s) \<Rightarrow> m \<Down> emb ps' s" 
proof (induct rule: big_step_t_part_induct) 
  case (Assign a x ps v ps')
  have z: "paval a ps = aval a (emb ps s)"
    apply(rule paval_aval_vars) using Assign(1) by auto
  have g :"emb ps' s = (emb ps s)(x:=aval a (emb ps s) )"
    apply(simp only: Assign z[symmetric])
      unfolding emb_def by auto      
  show ?case apply(simp only: g) by(rule big_step_t.Assign)
qed (auto simp: pbval_bval_vars[symmetric])
  
  
lemma part_to_full: "(C, part s) \<Rightarrow>\<^sub>A m \<Down> part s' \<Longrightarrow> (C, s) \<Rightarrow> m \<Down> s'"
proof -
  assume "(C, part s) \<Rightarrow>\<^sub>A m \<Down> part s'"
  then have "(C, emb (part s) s) \<Rightarrow> m \<Down> emb (part s') s" by (rule part_to_full')
  then show "(C, s) \<Rightarrow> m \<Down> s'" by auto
qed
  
  
lemma part_full_equiv: "(C, s) \<Rightarrow> m \<Down> s' \<longleftrightarrow> (C, part s) \<Rightarrow>\<^sub>A m \<Down> part s'"
using part_to_full full_to_part by metis    
    
subsubsection \<open>more properties\<close>
    
lemma big_step_t3_gt0: "(C, ps) \<Rightarrow>\<^sub>A x \<Down> ps' \<Longrightarrow> x > 0"
apply(induct rule: big_step_t_part_induct) apply auto done
        
lemma big_step_t3_same: "(C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' ==>  ps = ps' on UNIV - lvars C"
apply(induct rule: big_step_t_part_induct) by (auto simp: sep_disj_fun_def plus_fun_def) 
    
lemma avalDirekt3_correct: " (x ::= N v, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<Longrightarrow> paval' a ps = Some v \<Longrightarrow>  (x ::= a, ps) \<Rightarrow>\<^sub>A m \<Down> ps'" 
apply(auto) apply(subst Assign) by (auto simp: paval_paval' paval'dom) 
    


  
subsection \<open>Partial State\<close>    
  
 
  
(* partialstate and nat is a separation algebra ! *)  
lemma
  fixes h :: "(vname \<Rightarrow> val option) * nat"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)
        
lemma separate_othogonal_commuted': assumes
    "\<And>ps n. P (ps,n) \<Longrightarrow> ps = 0"
    "\<And>ps n. Q (ps,n) \<Longrightarrow> n = 0"
  shows "(P ** Q) s \<longleftrightarrow> P (0,snd s) \<and> Q (fst s,0)"
  using assms unfolding sep_conj_def by force  
   
 
lemma separate_othogonal_commuted: assumes
    "\<And>ps n. P (ps,n) \<Longrightarrow> ps = 0"
    "\<And>ps n. Q (ps,n) \<Longrightarrow> n = 0"
  shows "(P ** Q) (ps,n) \<longleftrightarrow> P (0,n) \<and> Q (ps,0)"
  using assms unfolding sep_conj_def by force  
   
    
lemma separate_othogonal: assumes
    "\<And>ps n. P (ps,n) \<Longrightarrow> n = 0"
    "\<And>ps n. Q (ps,n) \<Longrightarrow> ps = 0"
  shows "(P ** Q) (ps,n) \<longleftrightarrow> P (ps,0) \<and> Q (0,n)"
  using assms unfolding sep_conj_def by force 
    
lemma assumes "  ((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* (\<lambda>(s, c). s = 0 \<and> c = Suc 0)) (ps, n)"
shows "\<exists> n'. P (ps, n') \<and> vars b \<subseteq> dom ps \<and> n = Suc n'"
proof -
  from assms obtain x y where " x ## y" and "(ps, n) = x + y" 
      and 2: "(case x of (s, n) \<Rightarrow> P (s, n) \<and> vars b \<subseteq>  dom s)"
      and "(case y of (s, c) \<Rightarrow> s = 0 \<and> c = Suc 0)" 
    unfolding sep_conj_def by blast
  then have "y = (0, Suc 0)" and f: "fst x = ps" and n: "n = snd x + Suc 0" by auto
    
  with 2 have "P (ps, snd x) \<and> vars b \<subseteq> dom ps \<and> n = Suc (snd x)"
    by auto 
  then show ?thesis by simp
qed 
       
    
    
    
subsection \<open>Dollar and Pointsto\<close>    
    
definition dollar :: "nat \<Rightarrow> assn2" ("$") where
  "dollar q = (%(s,c). s = 0 \<and> c=q)"
  
  
lemma sep_reorder_dollar_aux:  
    "NO_MATCH ($X) A \<Longrightarrow> ($B ** A) = (A ** $B)"   
    "($X ** $Y) = $(X+Y)"
   apply (auto simp: sep_simplify)
    unfolding dollar_def sep_conj_def sep_disj_prod_def sep_disj_nat_def by auto
     
lemmas sep_reorder_dollar = sep_conj_assoc sep_reorder_dollar_aux

lemma stardiff: assumes "(P \<and>* $m) (ps, n)"
  shows  P: "P (ps, n - m)" and "m\<le>n" using assms unfolding sep_conj_def dollar_def by auto     

lemma [simp]: "(Q ** $0) = Q" unfolding dollar_def sep_conj_def sep_disj_prod_def sep_disj_nat_def  
  by auto 
  
definition embP :: "(partstate \<Rightarrow> bool) \<Rightarrow> partstate \<times> nat \<Rightarrow> bool" where "embP P = (%(s,n). P s \<and> n = 0)"
  
    
lemma orthogonal_split: assumes "(embP Q \<and>* $ n) = (embP P \<and>* $ m)"   
  shows "(Q = P \<and> n = m) \<or> Q = (\<lambda>s. False) \<and> P = (\<lambda>s. False)"
  using assms unfolding embP_def dollar_def apply (auto intro!: ext)
    unfolding sep_conj_def apply auto unfolding  sep_disj_prod_def  plus_prod_def  
    apply (metis fst_conv snd_conv)+ done
      
(* how to set up case rules *)      
      
lemma F: assumes "(embP Q \<and>* $ n) = (embP P \<and>* $ m)"   
  obtains (blub) "Q = P" and "n = m" |
          (da)  "Q = (\<lambda>s. False)" and "P = (\<lambda>s. False)" 
  using assms orthogonal_split by auto
    
lemma T: assumes "(embP Q \<and>* $ n) = (embP P \<and>* $ m)"   
  obtains (blub) x::nat where "Q = P" and "n = m" and "x=x" |
          (da)  "Q = (\<lambda>s. False)" and "P = (\<lambda>s. False)"
          using assms orthogonal_split by auto
  
  
definition pointsto :: "vname \<Rightarrow> val \<Rightarrow> assn2"  ("_ \<hookrightarrow> _" [56,51] 56) where
  "v \<hookrightarrow> n = (%(s,c). s = [v \<mapsto> n] \<and> c=0)"
  
(* If you don't mind syntax ambiguity: *)
notation pred_ex (binder "\<exists>" 10)
  
definition maps_to_ex :: "vname \<Rightarrow> assn2" ("_ \<hookrightarrow> -" [56] 56)
  where "x \<hookrightarrow> - \<equiv> \<exists>y. x \<hookrightarrow> y"
        
fun lmaps_to_ex :: "vname set \<Rightarrow> assn2" where
  "lmaps_to_ex xs = (%(s,c). dom s = xs \<and> c = 0)"
   
  
lemma "(x \<hookrightarrow> -) (s,n) \<Longrightarrow> x \<in> dom s"
  unfolding maps_to_ex_def pointsto_def by auto 
      
fun lmaps_to_axpr :: "bexp \<Rightarrow> bool \<Rightarrow> assnp" where
  "lmaps_to_axpr b bv = (%ps. vars b \<subseteq> dom ps \<and> pbval b ps = bv )"
 
definition lmaps_to_axpr' :: "bexp \<Rightarrow> bool \<Rightarrow> assnp" where
  "lmaps_to_axpr' b bv = lmaps_to_axpr b bv"
  
   
    
    
subsection \<open>Frame Inference\<close>
      
definition Frame where "Frame P Q F \<equiv>    \<forall>s. (P imp (Q ** F)) s" 
definition Frame' where "Frame' P P' Q F \<equiv> \<forall>s. (( P' ** P) imp (Q ** F)) s"  

definition cnv where "cnv x y == x = y"
  
lemma cnv_I: "cnv x x"
  unfolding cnv_def by simp
  
lemma Frame'_conv: "Frame P Q F = Frame' (P ** \<box>) \<box> (Q ** \<box>) F" 
  unfolding Frame_def Frame'_def apply auto done     
    
lemma Frame'I: "Frame' (P ** \<box>) \<box> (Q ** \<box>) F \<Longrightarrow> cnv F F' \<Longrightarrow> Frame P Q F'" 
  unfolding Frame_def Frame'_def cnv_def apply auto done
    
lemma FrameD: assumes "Frame P Q F" " P s "
  shows "(F ** Q) s"
  using assms unfolding Frame_def by (auto simp: sep_conj_commute)    
    
lemma Frame'_match: "Frame' (P ** P') \<box> Q F \<Longrightarrow> Frame' (x \<hookrightarrow> v ** P) P' (x \<hookrightarrow> v ** Q) F" 
  unfolding Frame_def Frame'_def apply (auto simp: sep_conj_ac)
  by (metis (no_types, hide_lams) prod.collapse sep.mult_assoc sep_conj_impl1)   
    
lemma R: assumes "\<And>s. (A imp B) s" shows "((A ** $n) imp (B ** $n)) s"    
proof (safe)
  assume "(A \<and>* $ n) s"
  then obtain h1 h2 where A: "A h1"  and n: "$n h2" and disj: "h1 ## h2" "s = h1+h2" unfolding sep_conj_def by blast
  from assms A have B: "B h1" by auto    
  show "(B ** $n) s" using B n disj unfolding sep_conj_def by blast
qed 
  
lemma Frame'_matchdollar:  assumes "Frame' (P ** P' ** $(n-m)) \<box> Q F" and nm: "n\<ge>m"
  shows "Frame' ($n ** P) P' ($m ** Q) F" 
 using assms(1) unfolding Frame_def Frame'_def apply (auto simp: sep_conj_ac)  
proof (goal_cases)
  case (1 a b) 
  have g: "((P \<and>* P' \<and>* $ n) imp (F \<and>* Q \<and>* $ m)) (a, b)
        \<longleftrightarrow> (((P \<and>* P' \<and>* $(n-m)) ** $m) imp ((F \<and>* Q) \<and>* $ m)) (a, b)" 
    by(simp add: nm sep_reorder_dollar)
  have "((P \<and>* P' \<and>* $ n) imp (F \<and>* Q \<and>* $ m)) (a, b)"     
    apply(subst g)
      apply(rule R) using 1(1) by auto
  then have "(P \<and>* P' \<and>* $ n) (a, b) \<longrightarrow> (F \<and>* Q \<and>* $ m) (a, b)"
    by blast  
  then show ?case using 1(2) by auto
qed
                                                            
lemma Frame'_nomatch: " Frame' P (p ** P') (x \<hookrightarrow> v ** Q) F\<Longrightarrow> Frame' (p ** P) P' (x \<hookrightarrow> v ** Q) F" 
  unfolding  Frame'_def by (auto simp: sep_conj_ac)   
    
lemma Frame'_nomatchempty: " Frame' P P' (x \<hookrightarrow> v ** Q) F\<Longrightarrow> Frame' (\<box> ** P) P' (x \<hookrightarrow> v ** Q) F" 
  unfolding  Frame'_def by (auto simp: sep_conj_ac) 
        
(* this will only be reached after a Frame'_match move, where P' is \<box> *)    
lemma Frame'_end: " Frame' P \<box> \<box> P"
  unfolding  Frame'_def by (auto simp: sep_conj_ac)   
        
schematic_goal "Frame (x \<hookrightarrow> v1 \<and>* y \<hookrightarrow> v2)  (x \<hookrightarrow> ?v) ?F"
  apply(rule Frame'I) apply(simp only: sep_conj_assoc)
  apply(rule Frame'_match)
  apply(rule Frame'_end) apply(simp only: sep_conj_ac sep_conj_empty' sep_conj_empty) apply(rule cnv_I) done
    
schematic_goal "Frame (x \<hookrightarrow> v1 \<and>* y \<hookrightarrow> v2)  (y \<hookrightarrow> ?v) ?F"
  apply(rule Frame'I) apply(simp only: sep_conj_assoc)
   apply(rule Frame'_end Frame'_match Frame'_nomatchempty Frame'_nomatch; (simp only: sep_conj_assoc)?)+
    apply(simp only: sep_conj_ac sep_conj_empty' sep_conj_empty) apply(rule cnv_I) 
   done
        
method frame_inference_init = (rule Frame'I, (simp only: sep_conj_assoc)?)

method frame_inference_solve = (rule Frame'_matchdollar Frame'_end Frame'_match Frame'_nomatchempty Frame'_nomatch; (simp only: sep_conj_assoc)?)+
  
method frame_inference_cleanup = ( (simp only: sep_conj_ac sep_conj_empty' sep_conj_empty)?; rule cnv_I)
  
  
method frame_inference = (frame_inference_init, (frame_inference_solve; fail), (frame_inference_cleanup; fail))
method frame_inference_debug = (frame_inference_init, frame_inference_solve)
  
subsubsection \<open>tests\<close>  
      
schematic_goal "Frame (x \<hookrightarrow> v1 \<and>* y \<hookrightarrow> v2)  (y \<hookrightarrow> ?v) ?F"
  by frame_inference
    
schematic_goal "Frame (x \<hookrightarrow> v1 ** P ** \<box> ** y \<hookrightarrow> v2 \<and>* z \<hookrightarrow> v2 ** Q)  (z \<hookrightarrow> ?v ** y \<hookrightarrow> ?v2) ?F"
  by frame_inference
          
(* with dollar *)

schematic_goal " 1 \<le> v \<Longrightarrow> Frame ($ (2 * v) \<and>* ''x'' \<hookrightarrow> int v) ($ 1 \<and>* ''x'' \<hookrightarrow> ?d) ?F" 
  apply(rule Frame'I) apply(simp only: sep_conj_assoc) 
   apply(rule  Frame'_matchdollar Frame'_end Frame'_match Frame'_nomatchempty Frame'_nomatch; (simp only: sep_conj_assoc)?)+
  apply (simp only: sep_conj_ac sep_conj_empty' sep_conj_empty)?
  apply (rule cnv_I) done 
    
    
schematic_goal " 0 < v \<Longrightarrow> Frame ($ (2 * v) \<and>* ''x'' \<hookrightarrow> int v) ($ 1 \<and>* ''x'' \<hookrightarrow> ?d) ?F"    
    apply frame_inference done
            
subsection \<open>Expression evaluation\<close>
      
definition symeval where "symeval P e v \<equiv> (\<forall>s n. P (s,n) \<longrightarrow> paval' e s = Some v)"    
definition symevalb where "symevalb P e v \<equiv> (\<forall>s n. P (s,n) \<longrightarrow> pbval' e s = Some v)"      
      
lemma symeval_c: "symeval P (N v) v"
  unfolding symeval_def apply auto done
      
    
lemma symeval_v: assumes "Frame P (x \<hookrightarrow> v) F"
  shows "symeval P (V x) v"
  unfolding symeval_def apply auto
  apply (drule FrameD[OF assms])  unfolding sep_conj_def pointsto_def  
  apply (auto simp: plus_fun_conv) done
    
lemma symeval_plus: assumes "symeval P e1 v1" "symeval P e2 v2"
  shows "symeval P (Plus e1 e2) (v1+v2)"
  using assms unfolding symeval_def by auto 
    
    
lemma symevalb_c: "symevalb P (Bc v) v"
  unfolding symevalb_def apply auto done
          
lemma symevalb_and: assumes "symevalb P e1 v1" "symevalb P e2 v2"
  shows "symevalb P (And e1 e2) (v1 \<and> v2)"
  using assms unfolding symevalb_def  by auto
    
lemma symevalb_not:  assumes "symevalb P e v"
  shows "symevalb P (Not e) (\<not> v)"
  using assms unfolding symevalb_def  by auto
    
lemma symevalb_less: assumes "symeval P e1 v1" "symeval P e2 v2"
  shows "symevalb P (Less e1 e2) (v1 < v2)"
  using assms unfolding symevalb_def symeval_def by auto
  
lemmas symeval = symeval_c symeval_v symeval_plus symevalb_c symevalb_and symevalb_not symevalb_less
   
schematic_goal "symevalb ( (x \<hookrightarrow> v1) ** (y \<hookrightarrow> v2) ) (Less (Plus (V x) (V y)) (N 5)) ?g"
  apply(rule symeval | frame_inference)+ done
    
end