(*  Title:      HOL/MicroJava/BV/Opt.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

More about options.
*)

section \<open>More about Options\<close>

theory Opt
imports
  Err
begin

definition le :: "'a ord \<Rightarrow> 'a option ord"
where
  "le r o\<^sub>1 o\<^sub>2 =
  (case o\<^sub>2 of None \<Rightarrow> o\<^sub>1=None | Some y \<Rightarrow> (case o\<^sub>1 of None \<Rightarrow> True | Some x \<Rightarrow> x \<sqsubseteq>\<^sub>r y))"

definition opt :: "'a set \<Rightarrow> 'a option set"
where
  "opt A = insert None {Some y |y. y \<in> A}"

definition sup :: "'a ebinop \<Rightarrow> 'a option ebinop"
where
  "sup f o\<^sub>1 o\<^sub>2 =  
  (case o\<^sub>1 of None \<Rightarrow> OK o\<^sub>2 
           | Some x \<Rightarrow> (case o\<^sub>2 of None \<Rightarrow> OK o\<^sub>1
                                 | Some y \<Rightarrow> (case f x y of Err \<Rightarrow> Err | OK z \<Rightarrow> OK (Some z))))"

definition esl :: "'a esl \<Rightarrow> 'a option esl"
where
  "esl = (\<lambda>(A,r,f). (opt A, le r, sup f))"


lemma unfold_le_opt:
  "o\<^sub>1 \<sqsubseteq>\<^bsub>le r\<^esub> o\<^sub>2 = 
  (case o\<^sub>2 of None \<Rightarrow> o\<^sub>1=None | 
              Some y \<Rightarrow> (case o\<^sub>1 of None \<Rightarrow> True | Some x \<Rightarrow> x \<sqsubseteq>\<^sub>r y))"
(*<*)
apply (unfold lesub_def le_def)
apply (rule refl)
done
(*>*)

lemma le_opt_refl: "order r \<Longrightarrow> x \<sqsubseteq>\<^bsub>le r\<^esub> x"
(*<*) by (simp add: unfold_le_opt split: option.split) (*<*)

lemma le_opt_trans [rule_format]:
  "order r \<Longrightarrow> x \<sqsubseteq>\<^bsub>le r\<^esub> y \<longrightarrow> y \<sqsubseteq>\<^bsub>le r\<^esub> z \<longrightarrow> x \<sqsubseteq>\<^bsub>le r\<^esub> z"
(*<*)
apply (simp add: unfold_le_opt split: option.split)
apply (blast intro: order_trans)
done
(*>*)

lemma le_opt_antisym [rule_format]:
  "order r \<Longrightarrow> x \<sqsubseteq>\<^bsub>le r\<^esub> y \<longrightarrow> y \<sqsubseteq>\<^bsub>le r\<^esub> x \<longrightarrow> x=y"
(*<*)
apply (simp add: unfold_le_opt split: option.split)
apply (blast intro: order_antisym)
done
(*>*)

lemma order_le_opt [intro!,simp]: "order r \<Longrightarrow> order(le r)"
(*<*)
apply (subst order_def)
apply (blast intro: le_opt_refl le_opt_trans le_opt_antisym)
done 
(*>*)

lemma None_bot [iff]:  "None \<sqsubseteq>\<^bsub>le r\<^esub> ox"
(*<*)
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 
(*>*)

lemma Some_le [iff]: "(Some x \<sqsubseteq>\<^bsub>le r\<^esub> z) = (\<exists>y. z = Some y \<and> x \<sqsubseteq>\<^sub>r y)"
(*<*)
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 
(*>*)

lemma le_None [iff]: "(x \<sqsubseteq>\<^bsub>le r\<^esub> None) = (x = None)"
(*<*)
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 
(*>*)

lemma OK_None_bot [iff]: "OK None \<sqsubseteq>\<^bsub>Err.le (le r)\<^esub> x"
(*<*) by (simp add: lesub_def Err.le_def le_def split: option.split err.split) (*>*)

lemma sup_None1 [iff]: "x \<squnion>\<^bsub>sup f\<^esub> None = OK x"
(*<*) by (simp add: plussub_def sup_def split: option.split) (*>*)

lemma sup_None2 [iff]: "None \<squnion>\<^bsub>sup f\<^esub> x = OK x"
(*<*) by (simp add: plussub_def sup_def split: option.split) (*>*)

lemma None_in_opt [iff]: "None \<in> opt A"
(*<*) by (simp add: opt_def) (*>*)

lemma Some_in_opt [iff]: "(Some x \<in> opt A) = (x \<in> A)"
(*<*) by (unfold opt_def) auto (*>*)

lemma semilat_opt [intro, simp]:
  "err_semilat L \<Longrightarrow> err_semilat (Opt.esl L)"
(*<*)
proof -
  assume s: "err_semilat L" 
  obtain A r f where [simp]: "L = (A,r,f)" by (cases L)
  let ?A0 = "err A" and ?r0 = "Err.le r" and ?f0 = "lift2 f"
  from s obtain
    ord: "order ?r0" and
    clo: "closed ?A0 ?f0" and
    ub1: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. x \<sqsubseteq>\<^bsub>?r0\<^esub> x \<squnion>\<^bsub>?f0\<^esub> y" and
    ub2: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. y \<sqsubseteq>\<^bsub>?r0\<^esub> x \<squnion>\<^bsub>?f0\<^esub> y" and
    lub: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. \<forall>z\<in>?A0. x \<sqsubseteq>\<^bsub>?r0\<^esub> z \<and> y \<sqsubseteq>\<^bsub>?r0\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>?f0\<^esub> y \<sqsubseteq>\<^bsub>?r0\<^esub> z"
    by (unfold semilat_def sl_def) simp

  let ?A = "err (opt A)" and ?r = "Err.le (Opt.le r)" and ?f = "lift2 (Opt.sup f)"

  from ord have "order ?r" by simp
  moreover
  have "closed ?A ?f"
  proof (unfold closed_def, intro strip)
    fix x y assume x: "x \<in> ?A" and y: "y \<in> ?A" 

    { fix a b assume ab: "x = OK a" "y = OK b"
      with x have a: "\<And>c. a = Some c \<Longrightarrow> c \<in> A" by (clarsimp simp add: opt_def)
      from ab y have b: "\<And>d. b = Some d \<Longrightarrow> d \<in> A" by (clarsimp simp add: opt_def)      
      { fix c d assume "a = Some c" "b = Some d"
        with ab x y have "c \<in> A & d \<in> A" by (simp add: err_def opt_def Bex_def)
        with clo have "f c d \<in> err A" 
          by (simp add: closed_def plussub_def err_def' lift2_def)
        moreover fix z assume "f c d = OK z"
        ultimately have "z \<in> A" by simp
      } note f_closed = this    
      have "sup f a b \<in> ?A"
      proof (cases a)
        case None thus ?thesis
          by (simp add: sup_def opt_def) (cases b, simp, simp add: b Bex_def)
      next
        case Some thus ?thesis
          by (auto simp add: sup_def opt_def Bex_def a b f_closed split: err.split option.split)
      qed
    }
    thus "x \<squnion>\<^bsub>?f\<^esub> y \<in> ?A" by (simp add: plussub_def lift2_def split: err.split)
  qed
  moreover
  { fix a b c assume "a \<in> opt A" and "b \<in> opt A" and "a \<squnion>\<^bsub>sup f\<^esub> b = OK c" 
    moreover from ord have "order r" by simp
    moreover
    { fix x y z assume "x \<in> A" and "y \<in> A" 
      hence "OK x \<in> err A \<and> OK y \<in> err A" by simp
      with ub1 ub2
      have "(OK x) \<sqsubseteq>\<^bsub>Err.le r\<^esub> (OK x) \<squnion>\<^bsub>lift2 f\<^esub> (OK y) \<and>
            (OK y) \<sqsubseteq>\<^bsub>Err.le r\<^esub> (OK x) \<squnion>\<^bsub>lift2 f\<^esub> (OK y)"
        by blast
      moreover assume "x \<squnion>\<^sub>f y = OK z"
      ultimately have "x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z"
        by (auto simp add: plussub_def lift2_def Err.le_def lesub_def)
    }
    ultimately have "a \<sqsubseteq>\<^bsub>le r\<^esub> c \<and> b \<sqsubseteq>\<^bsub>le r\<^esub> c"
      by (auto simp add: sup_def le_def lesub_def plussub_def 
               dest: order_refl split: option.splits err.splits)
  }     
  hence "(\<forall>x\<in>?A. \<forall>y\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> x \<squnion>\<^bsub>?f\<^esub> y) \<and> (\<forall>x\<in>?A. \<forall>y\<in>?A. y \<sqsubseteq>\<^bsub>?r\<^esub> x \<squnion>\<^bsub>?f\<^esub> y)"
    by (auto simp add: lesub_def plussub_def Err.le_def lift2_def split: err.split)
  moreover
  have "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> z \<and> y \<sqsubseteq>\<^bsub>?r\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>?f\<^esub> y \<sqsubseteq>\<^bsub>?r\<^esub> z"
  proof (intro strip, elim conjE)
    fix x y z
    assume xyz: "x \<in> ?A"   "y \<in> ?A"   "z \<in> ?A"
    assume xz: "x \<sqsubseteq>\<^bsub>?r\<^esub> z" and yz: "y \<sqsubseteq>\<^bsub>?r\<^esub> z"
    { fix a b c assume ok: "x = OK a"  "y = OK b"  "z = OK c"
      { fix d e g  assume some: "a = Some d"  "b = Some e"  "c = Some g"
        with ok xyz obtain "OK d:err A" "OK e:err A" "OK g:err A"  by simp
        with lub  
        have "\<lbrakk> OK d \<sqsubseteq>\<^bsub>Err.le r\<^esub> OK g; OK e \<sqsubseteq>\<^bsub>Err.le r\<^esub> OK g \<rbrakk> \<Longrightarrow> OK d \<squnion>\<^bsub>lift2 f\<^esub> OK e \<sqsubseteq>\<^bsub>Err.le r\<^esub> OK g"
          by blast
        hence "\<lbrakk> d \<sqsubseteq>\<^sub>r g; e \<sqsubseteq>\<^sub>r g \<rbrakk> \<Longrightarrow> \<exists>y. d \<squnion>\<^sub>f e = OK y \<and> y \<sqsubseteq>\<^sub>r g" by simp
        with ok some xyz xz yz have "x \<squnion>\<^bsub>?f\<^esub> y \<sqsubseteq>\<^bsub>?r\<^esub> z"
          by (auto simp add: sup_def le_def lesub_def lift2_def plussub_def Err.le_def)
      } note this [intro!]
      from ok xyz xz yz have "x \<squnion>\<^bsub>?f\<^esub> y \<sqsubseteq>\<^bsub>?r\<^esub> z"
        by - (cases a, simp, cases b, simp, cases c, simp, blast)
    }    
    with xyz xz yz show "x \<squnion>\<^bsub>?f\<^esub> y \<sqsubseteq>\<^bsub>?r\<^esub> z"
      by - (cases x, simp, cases y, simp, cases z, simp+)
  qed
  ultimately show "err_semilat (Opt.esl L)"
    by (unfold semilat_def esl_def sl_def) simp
qed 
(*>*)

lemma top_le_opt_Some [iff]: "top (le r) (Some T) = top r T"
(*<*)
apply (unfold top_def)
apply (rule iffI)
 apply blast
apply (rule allI)
apply (case_tac "x")
apply simp+
done 
(*>*)

lemma Top_le_conv:  "\<lbrakk> order r; top r T \<rbrakk> \<Longrightarrow> (T \<sqsubseteq>\<^sub>r x) = (x = T)"
(*<*)
apply (unfold top_def)
apply (blast intro: order_antisym)
done 
(*>*)


lemma acc_le_optI [intro!]: "acc A r \<Longrightarrow> acc (opt A) (le r)"
(*<*)
apply (unfold acc_def lesub_def le_def lesssub_def)
apply (simp add: wf_eq_minimal split: option.split)
apply clarify
apply (case_tac "\<exists>a. Some a \<in> Q")
 apply (erule_tac x = "{a . Some a \<in> Q}" in allE)
 apply blast
apply (case_tac "x")
 apply blast
apply blast
done 
(*>*)

lemma map_option_in_optionI:
  "\<lbrakk> ox \<in> opt S; \<forall>x\<in>S. ox = Some x \<longrightarrow> f x \<in> S \<rbrakk> 
  \<Longrightarrow> map_option f ox \<in> opt S"
(*<*)
apply (unfold map_option_case)
apply (simp split: option.split)
apply blast
done 
(*>*)

end
