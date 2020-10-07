(*  Title:      HOL/MicroJava/BV/Typing_Framework_err.thy
    Author:     Gerwin Klein
    Copyright   2000 TUM

*)

section \<open>Lifting the Typing Framework to err, app, and eff\<close>

theory Typing_Framework_err imports Typing_Framework SemilatAlg begin

definition wt_err_step :: "'s ord \<Rightarrow> 's err step_type \<Rightarrow> 's err list \<Rightarrow> bool"
where
  "wt_err_step r step \<tau>s \<longleftrightarrow> wt_step (Err.le r) Err step \<tau>s"

definition wt_app_eff :: "'s ord \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
where
  "wt_app_eff r app step \<tau>s \<longleftrightarrow>
    (\<forall>p < size \<tau>s. app p (\<tau>s!p) \<and> (\<forall>(q,\<tau>) \<in> set (step p (\<tau>s!p)). \<tau> <=_r \<tau>s!q))"

definition map_snd :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list"
where
  "map_snd f = map (\<lambda>(x,y). (x, f y))"

definition error :: "nat \<Rightarrow> (nat \<times> 'a err) list"
where
  "error n = map (\<lambda>x. (x,Err)) [0..<n]"

definition err_step :: "nat \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's step_type \<Rightarrow> 's err step_type"
where
  "err_step n app step p t = 
  (case t of 
    Err   \<Rightarrow> error n
  | OK \<tau> \<Rightarrow> if app p \<tau> then map_snd OK (step p \<tau>) else error n)"

definition app_mono :: "'s ord \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
where
  "app_mono r app n A \<longleftrightarrow>
    (\<forall>s p t. s \<in> A \<and> p < n \<and> s \<sqsubseteq>\<^sub>r t \<longrightarrow> app p t \<longrightarrow> app p s)"


lemmas err_step_defs = err_step_def map_snd_def error_def


lemma bounded_err_stepD:
  "\<lbrakk> bounded (err_step n app step) n;
     p < n; app p a; (q,b) \<in> set (step p a) \<rbrakk> \<Longrightarrow> q < n"
(*<*)
  apply (simp add: bounded_def err_step_def)
  apply (erule allE, erule impE, assumption)
  apply (erule_tac x = "OK a" in allE, drule bspec)
   apply (simp add: map_snd_def)
   apply fast
  apply simp
  done
(*>*)


lemma in_map_sndD: "(a,b) \<in> set (map_snd f xs) \<Longrightarrow> \<exists>b'. (a,b') \<in> set xs"
(*<*)
  apply (induct xs)
  apply (auto simp add: map_snd_def)
  done
(*>*)


lemma bounded_err_stepI:
  "\<forall>p. p < n \<longrightarrow> (\<forall>s. ap p s \<longrightarrow> (\<forall>(q,s') \<in> set (step p s). q < n))
  \<Longrightarrow> bounded (err_step n ap step) n"
(*<*)
apply (clarsimp simp: bounded_def err_step_def split: err.splits)
apply (simp add: error_def image_def)
apply (blast dest: in_map_sndD)
done
(*>*)


lemma bounded_lift:
  "bounded step n \<Longrightarrow> bounded (err_step n app step) n"
(*<*)
  apply (unfold bounded_def err_step_def error_def)
  apply clarify
  apply (erule allE, erule impE, assumption)
  apply (case_tac \<tau>)
  apply (auto simp add: map_snd_def split: if_split_asm)
  done
(*>*)


lemma le_list_map_OK [simp]:
  "\<And>b. (map OK a [\<sqsubseteq>\<^bsub>Err.le r\<^esub>] map OK b) = (a [\<sqsubseteq>\<^sub>r] b)"
(*<*)
  apply (induct a)
   apply simp
  apply simp
  apply (case_tac b)
   apply simp
  apply simp
  done
(*>*)


lemma map_snd_lessI:
  "set xs {\<sqsubseteq>\<^bsub>r\<^esub>} set ys \<Longrightarrow> set (map_snd OK xs) {\<sqsubseteq>\<^bsub>Err.le r\<^esub>} set (map_snd OK ys)"
(*<*)
  apply (induct xs)
  apply (unfold lesubstep_type_def map_snd_def)
  apply auto
  done
(*>*)


lemma mono_lift:
  "\<lbrakk> order r; app_mono r app n A; bounded (err_step n app step) n;
    \<forall>s p t. s \<in> A \<and> p < n \<and> s \<sqsubseteq>\<^sub>r t \<longrightarrow> app p t \<longrightarrow> set (step p s) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step p t) \<rbrakk>
  \<Longrightarrow>  mono (Err.le r) (err_step n app step) n (err A)"
(*<*)
apply (simp only: app_mono_def SemilatAlg.mono_def err_step_def)
apply clarify
apply (case_tac \<tau>)
 apply simp 
apply simp
apply (case_tac \<tau>')
 apply simp
 apply clarify
 apply (simp add: lesubstep_type_def error_def)
 apply clarify
 apply (drule in_map_sndD)
 apply clarify
 apply (drule bounded_err_stepD, assumption+)
 apply (rule exI [of _ Err])
 apply simp
apply simp
apply (erule allE, erule allE, erule allE, erule impE)
 apply (rule conjI, assumption)
 apply (rule conjI, assumption)
 apply assumption
apply (rule conjI)
apply clarify
apply (erule allE, erule allE, erule allE, erule impE)
 apply (rule conjI, assumption)
 apply (rule conjI, assumption)
 apply assumption
apply (erule impE, assumption)
apply (rule map_snd_lessI, assumption)
apply clarify
apply (simp add: lesubstep_type_def error_def)
apply clarify
apply (drule in_map_sndD)
apply clarify
apply (drule bounded_err_stepD, assumption+)
apply (rule exI [of _ Err])
apply simp
done
(*>*)
 
lemma in_errorD: "(x,y) \<in> set (error n) \<Longrightarrow> y = Err"
(*<*) by (auto simp add: error_def) (*>*)

lemma pres_type_lift:
  "\<forall>s\<in>A. \<forall>p. p < n \<longrightarrow> app p s \<longrightarrow> (\<forall>(q, s')\<in>set (step p s). s' \<in> A) 
  \<Longrightarrow> pres_type (err_step n app step) n (err A)"  
(*<*)
apply (unfold pres_type_def err_step_def)
apply clarify
apply (case_tac b)
 apply simp
apply (case_tac \<tau>)
 apply simp
 apply (drule in_errorD)
 apply simp
apply (simp add: map_snd_def split: if_split_asm)
 apply fast
apply (drule in_errorD)
apply simp
done
(*>*)


lemma wt_err_imp_wt_app_eff:
  assumes wt: "wt_err_step r (err_step (size ts) app step) ts"
  assumes b:  "bounded (err_step (size ts) app step) (size ts)"
  shows "wt_app_eff r app step (map ok_val ts)"
(*<*)
proof (unfold wt_app_eff_def, intro strip, rule conjI)
  fix p assume "p < size (map ok_val ts)"
  hence lp: "p < size ts" by simp
  hence ts: "0 < size ts" by (cases p) auto
  hence err: "(0,Err) \<in> set (error (size ts))" by (simp add: error_def)

  from wt lp
  have [intro?]: "\<And>p. p < size ts \<Longrightarrow> ts ! p \<noteq> Err" 
    by (unfold wt_err_step_def wt_step_def) simp

  show app: "app p (map ok_val ts ! p)"
  proof (rule ccontr)
    from wt lp obtain s where
      OKp:  "ts ! p = OK s" and
      less: "\<forall>(q,t) \<in> set (err_step (size ts) app step p (ts!p)). t <=_(Err.le r) ts!q"
      by (unfold wt_err_step_def wt_step_def stable_def) 
         (auto iff: not_Err_eq)
    assume "\<not> app p (map ok_val ts ! p)"
    with OKp lp have "\<not> app p s" by simp
    with OKp have "err_step (size ts) app step p (ts!p) = error (size ts)" 
      by (simp add: err_step_def)    
    with err ts obtain q where 
      "(q,Err) \<in> set (err_step (size ts) app step p (ts!p))" and
      q: "q < size ts" by auto    
    with less have "ts!q = Err" by auto
    moreover from q have "ts!q \<noteq> Err" ..
    ultimately show False by blast
  qed
  
  show "\<forall>(q,t)\<in>set(step p (map ok_val ts ! p)). t \<sqsubseteq>\<^sub>r map ok_val ts ! q" 
  proof clarify
    fix q t assume q: "(q,t) \<in> set (step p (map ok_val ts ! p))"

    from wt lp q
    obtain s where
      OKp:  "ts ! p = OK s" and
      less: "\<forall>(q,t) \<in> set (err_step (size ts) app step p (ts!p)). t <=_(Err.le r) ts!q"
      by (unfold wt_err_step_def wt_step_def stable_def) 
         (auto iff: not_Err_eq)

    from b lp app q have lq: "q < size ts" by (rule bounded_err_stepD)
    hence "ts!q \<noteq> Err" ..
    then obtain s' where OKq: "ts ! q = OK s'" by (auto iff: not_Err_eq)

    from lp lq OKp OKq app less q
    show "t \<sqsubseteq>\<^sub>r map ok_val ts ! q"
      by (auto simp add: err_step_def map_snd_def) 
  qed
qed
(*>*)


lemma wt_app_eff_imp_wt_err:
  assumes app_eff: "wt_app_eff r app step ts"
  assumes bounded: "bounded (err_step (size ts) app step) (size ts)"
  shows "wt_err_step r (err_step (size ts) app step) (map OK ts)"
(*<*)
proof (unfold wt_err_step_def wt_step_def, intro strip, rule conjI)
  fix p assume "p < size (map OK ts)" 
  hence p: "p < size ts" by simp
  thus "map OK ts ! p \<noteq> Err" by simp
  { fix q t
    assume q: "(q,t) \<in> set (err_step (size ts) app step p (map OK ts ! p))" 
    with p app_eff obtain 
      "app p (ts ! p)" "\<forall>(q,t) \<in> set (step p (ts!p)). t \<sqsubseteq>\<^sub>r ts!q"
      by (unfold wt_app_eff_def) blast
    moreover
    from q p bounded have "q < size ts"
      by - (rule boundedD)
    hence "map OK ts ! q = OK (ts!q)" by simp
    moreover
    have "p < size ts" by (rule p)
    moreover note q
    ultimately     
    have "t \<sqsubseteq>\<^bsub>Err.le r\<^esub> map OK ts ! q" 
      by (auto simp add: err_step_def map_snd_def)
  }
  thus "stable (Err.le r) (err_step (size ts) app step) (map OK ts) p"
    by (unfold stable_def) blast
qed
(*>*)

end

