theory Semantics
imports Main
begin

section \<open>The Language\<close>

subsection \<open>Variables and Values\<close>

type_synonym vname = string \<comment> \<open>names for variables\<close>

datatype val
  = Bool bool      \<comment> \<open>Boolean value\<close>
  | Intg int       \<comment> \<open>integer value\<close> 

abbreviation "true == Bool True"
abbreviation "false == Bool False"



subsection \<open>Expressions and Commands\<close>

datatype bop = Eq | And | Less | Add | Sub     \<comment> \<open>names of binary operations\<close>

datatype expr
  = Val val                                          \<comment> \<open>value\<close>
  | Var vname                                        \<comment> \<open>local variable\<close>
  | BinOp expr bop expr    ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)  \<comment> \<open>binary operation\<close>


text \<open>Note: we assume that only type correct expressions are regarded
  as later proofs fail if expressions evaluate to None due to type errors.
  However there is [yet] no typing system\<close>

fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where "binop Eq v\<^sub>1 v\<^sub>2               = Some(Bool(v\<^sub>1 = v\<^sub>2))"
  | "binop And (Bool b\<^sub>1) (Bool b\<^sub>2)  = Some(Bool(b\<^sub>1 \<and> b\<^sub>2))"
  | "binop Less (Intg i\<^sub>1) (Intg i\<^sub>2) = Some(Bool(i\<^sub>1 < i\<^sub>2))"
  | "binop Add (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 + i\<^sub>2))"
  | "binop Sub (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 - i\<^sub>2))"

  | "binop bop v\<^sub>1 v\<^sub>2                = Some(Intg(0))"


datatype com
  = Skip
  | LAss vname expr        ("_:=_" [70,70] 70)  \<comment> \<open>local assignment\<close>
  | Seq com com            ("_;;/ _" [61,60] 60)
  | Cond expr com com      ("if '(_') _/ else _" [80,79,79] 70)
  | While expr com         ("while '(_') _" [80,79] 70)


fun fv :: "expr \<Rightarrow> vname set" \<comment> \<open>free variables in an expression\<close>
where
  FVc: "fv (Val V) = {}"
  | FVv: "fv (Var V) = {V}"
  | FVe: "fv (e1 \<guillemotleft>bop\<guillemotright> e2) = fv e1 \<union> fv e2"


subsection \<open>State\<close>

type_synonym state = "vname \<rightharpoonup> val"


text \<open>\<open>interpret\<close> silently assumes type correct expressions, 
  i.e. no expression evaluates to None\<close>

fun "interpret" :: "expr \<Rightarrow> state \<Rightarrow> val option" ("\<lbrakk>_\<rbrakk>_")
where Val: "\<lbrakk>Val v\<rbrakk> s = Some v"
  | Var: "\<lbrakk>Var V\<rbrakk> s = s V"
  | BinOp: "\<lbrakk>e\<^sub>1\<guillemotleft>bop\<guillemotright>e\<^sub>2\<rbrakk> s = (case \<lbrakk>e\<^sub>1\<rbrakk> s of None \<Rightarrow> None
    | Some v\<^sub>1 \<Rightarrow> (case \<lbrakk>e\<^sub>2\<rbrakk> s of None \<Rightarrow> None
                           | Some v\<^sub>2 \<Rightarrow> binop bop v\<^sub>1 v\<^sub>2))"

subsection \<open>Small Step Semantics\<close>

inductive red :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"
and red' :: "com \<Rightarrow> state \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool"
   ("((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
where
  "\<langle>c1,s1\<rangle> \<rightarrow> \<langle>c2,s2\<rangle> == red (c1,s1) (c2,s2)" |
  RedLAss:
  "\<langle>V:=e,s\<rangle> \<rightarrow> \<langle>Skip,s(V:=(\<lbrakk>e\<rbrakk> s))\<rangle>"

  | SeqRed:
  "\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s'\<rangle> \<Longrightarrow> \<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>1';;c\<^sub>2,s'\<rangle>"

  | RedSeq:
  "\<langle>Skip;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<rangle>"

  | RedCondTrue:
  "\<lbrakk>b\<rbrakk> s = Some true \<Longrightarrow> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>1,s\<rangle>"

  | RedCondFalse:
  "\<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<rangle>"

  | RedWhileTrue:
  "\<lbrakk>b\<rbrakk> s = Some true \<Longrightarrow> \<langle>while (b) c,s\<rangle> \<rightarrow> \<langle>c;;while (b) c,s\<rangle>"

  | RedWhileFalse:
  "\<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> \<langle>while (b) c,s\<rangle> \<rightarrow> \<langle>Skip,s\<rangle>"

lemmas red_induct = red.induct[split_format (complete)]

abbreviation reds ::"com \<Rightarrow> state \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" 
   ("((1\<langle>_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81) where
  "\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle> ==  red\<^sup>*\<^sup>* (c,s) (c',s')"

lemma Skip_reds:
  "\<langle>Skip,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle> \<Longrightarrow> s = s' \<and> c' = Skip"
by(blast elim:converse_rtranclpE red.cases)

lemma LAss_reds:
  "\<langle>V:=e,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> s' = s(V:=\<lbrakk>e\<rbrakk> s)"
proof(induct "V:=e" s rule:converse_rtranclp_induct2)
  case (step s c'' s'')
  hence "c'' = Skip" and "s'' = s(V:=(\<lbrakk>e\<rbrakk> s))" by(auto elim:red.cases)
  with \<open>\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>\<close> show ?case by(auto dest:Skip_reds)
qed

lemma Seq2_reds:
  "\<langle>Skip;;c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<langle>c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
by(induct c=="Skip;;c\<^sub>2" s rule:converse_rtranclp_induct2)(auto elim:red.cases)

lemma Seq_reds:
  assumes "\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
  obtains s'' where "\<langle>c\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Skip,s''\<rangle>" and "\<langle>c\<^sub>2,s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
proof -
  have "\<exists>s''. \<langle>c\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Skip,s''\<rangle> \<and> \<langle>c\<^sub>2,s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
  proof -
    { fix c c'
      assume "\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>" and "c = c\<^sub>1;;c\<^sub>2" and "c' = Skip"
      hence "\<exists>s''. \<langle>c\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Skip,s''\<rangle> \<and> \<langle>c\<^sub>2,s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
      proof(induct arbitrary:c\<^sub>1 rule:converse_rtranclp_induct2)
        case refl thus ?case by simp
      next
        case (step c s c'' s'')
        note IH = \<open>\<And>c\<^sub>1. \<lbrakk>c'' = c\<^sub>1;;c\<^sub>2; c' = Skip\<rbrakk> 
          \<Longrightarrow> \<exists>sx. \<langle>c\<^sub>1,s''\<rangle> \<rightarrow>* \<langle>Skip,sx\<rangle> \<and> \<langle>c\<^sub>2,sx\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>\<close>
        from step
        have "\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c'',s''\<rangle>" by simp
        hence "(c\<^sub>1 = Skip \<and> c'' = c\<^sub>2 \<and> s = s'') \<or> 
          (\<exists>c\<^sub>1'. \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle> \<and> c'' = c\<^sub>1';;c\<^sub>2)"
          by(auto elim:red.cases)
        thus ?case
        proof
          assume "c\<^sub>1 = Skip \<and> c'' = c\<^sub>2 \<and> s = s''"
          with \<open>\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>\<close> \<open>c' = Skip\<close>
          show ?thesis by auto
        next
          assume "\<exists>c\<^sub>1'. \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle> \<and> c'' = c\<^sub>1';;c\<^sub>2"
          then obtain c\<^sub>1' where "\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>" and "c'' = c\<^sub>1';;c\<^sub>2" by blast
          from IH[OF \<open>c'' = c\<^sub>1';;c\<^sub>2\<close> \<open>c' = Skip\<close>]
          obtain sx where "\<langle>c\<^sub>1',s''\<rangle> \<rightarrow>* \<langle>Skip,sx\<rangle>" and "\<langle>c\<^sub>2,sx\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
            by blast
          from \<open>\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>\<close> \<open>\<langle>c\<^sub>1',s''\<rangle> \<rightarrow>* \<langle>Skip,sx\<rangle>\<close>
          have "\<langle>c\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Skip,sx\<rangle>" by(auto intro:converse_rtranclp_into_rtranclp)
          with \<open>\<langle>c\<^sub>2,sx\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>\<close> show ?thesis by auto
        qed
      qed }
    with \<open>\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>\<close> show ?thesis by simp
  qed
  with that show ?thesis by blast
qed


lemma Cond_True_or_False:
  "\<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some true \<or> \<lbrakk>b\<rbrakk> s = Some false"
by(induct c=="if (b) c\<^sub>1 else c\<^sub>2" s rule:converse_rtranclp_induct2)(auto elim:red.cases)

lemma CondTrue_reds:
  "\<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some true \<Longrightarrow> \<langle>c\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
by(induct c=="if (b) c\<^sub>1 else c\<^sub>2" s rule:converse_rtranclp_induct2)(auto elim:red.cases)

lemma CondFalse_reds:
  "\<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> \<langle>c\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
by(induct c=="if (b) c\<^sub>1 else c\<^sub>2" s rule:converse_rtranclp_induct2)(auto elim:red.cases)

lemma WhileFalse_reds: 
  "\<langle>while (b) cx,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> s = s'"
proof(induct "while (b) cx" s rule:converse_rtranclp_induct2)
  case step thus ?case by(auto elim:red.cases dest: Skip_reds)
qed

lemma WhileTrue_reds: 
  "\<langle>while (b) cx,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some true
  \<Longrightarrow> \<exists>sx. \<langle>cx,s\<rangle> \<rightarrow>* \<langle>Skip,sx\<rangle> \<and> \<langle>while (b) cx,sx\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>"
proof(induct "while (b) cx" s rule:converse_rtranclp_induct2)
  case (step s c'' s'')
  hence "c'' = cx;;while (b) cx \<and> s'' = s" by(auto elim:red.cases)
  with \<open>\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>\<close> show ?case by(auto dest:Seq_reds)
qed

lemma While_True_or_False:
  "\<langle>while (b) com,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle> \<Longrightarrow> \<lbrakk>b\<rbrakk> s = Some true \<or> \<lbrakk>b\<rbrakk> s = Some false"
by(induct c=="while (b) com" s rule:converse_rtranclp_induct2)(auto elim:red.cases)


inductive red_n :: "com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool"
   ("((1\<langle>_,/_\<rangle>) \<rightarrow>\<^bsup>_\<^esup> (1\<langle>_,/_\<rangle>))" [0,0,0,0,0] 81)
where red_n_Base: "\<langle>c,s\<rangle> \<rightarrow>\<^bsup>0\<^esup> \<langle>c,s\<rangle>"
     | red_n_Rec: "\<lbrakk>\<langle>c,s\<rangle> \<rightarrow> \<langle>c'',s''\<rangle>; \<langle>c'',s''\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>c',s'\<rangle>\<rbrakk> \<Longrightarrow> \<langle>c,s\<rangle> \<rightarrow>\<^bsup>Suc n\<^esup> \<langle>c',s'\<rangle>"


lemma Seq_red_nE: assumes "\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>"
  obtains i j s'' where "\<langle>c\<^sub>1,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle>" and "\<langle>c\<^sub>2,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>"
  and "n = i + j + 1"
proof -
  from \<open>\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>\<close> 
  have "\<exists>i j s''. \<langle>c\<^sub>1,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle> \<and> \<langle>c\<^sub>2,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle> \<and> n = i + j + 1"
  proof(induct "c\<^sub>1;;c\<^sub>2" s n "Skip" s' arbitrary:c\<^sub>1 rule:red_n.induct)
    case (red_n_Rec s c'' s'' n s')
    note IH = \<open>\<And>c\<^sub>1. c'' = c\<^sub>1;;c\<^sub>2
      \<Longrightarrow> \<exists>i j sx. \<langle>c\<^sub>1,s''\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,sx\<rangle> \<and> \<langle>c\<^sub>2,sx\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle> \<and> n = i + j + 1\<close>
    from \<open>\<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c'',s''\<rangle>\<close>
    have "(c\<^sub>1 = Skip \<and> c'' = c\<^sub>2 \<and> s = s'') \<or> 
      (\<exists>c\<^sub>1'. c'' = c\<^sub>1';;c\<^sub>2 \<and> \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>)"
      by(induct "c\<^sub>1;;c\<^sub>2" _ _ _ rule:red_induct) auto
    thus ?case
    proof
      assume "c\<^sub>1 = Skip \<and> c'' = c\<^sub>2 \<and> s = s''"
      hence "c\<^sub>1 = Skip" and "c'' = c\<^sub>2" and "s = s''" by simp_all
      from \<open>c\<^sub>1 = Skip\<close> have "\<langle>c\<^sub>1,s\<rangle> \<rightarrow>\<^bsup>0\<^esup> \<langle>Skip,s\<rangle>" by(fastforce intro:red_n_Base)
      with \<open>\<langle>c'',s''\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>\<close> \<open>c'' = c\<^sub>2\<close> \<open>s = s''\<close>
      show ?thesis by(rule_tac x="0" in exI) auto
    next
      assume "\<exists>c\<^sub>1'. c'' = c\<^sub>1';;c\<^sub>2 \<and> \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>"
      then obtain c\<^sub>1' where "c'' = c\<^sub>1';;c\<^sub>2" and "\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>" by blast
      from IH[OF \<open>c'' = c\<^sub>1';;c\<^sub>2\<close>] obtain i j sx
        where "\<langle>c\<^sub>1',s''\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,sx\<rangle>" and "\<langle>c\<^sub>2,sx\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>"
        and "n = i + j + 1" by blast
      from \<open>\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s''\<rangle>\<close> \<open>\<langle>c\<^sub>1',s''\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,sx\<rangle>\<close>
      have "\<langle>c\<^sub>1,s\<rangle> \<rightarrow>\<^bsup>Suc i\<^esup> \<langle>Skip,sx\<rangle>" by(rule red_n.red_n_Rec)
      with \<open>\<langle>c\<^sub>2,sx\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>\<close> \<open>n = i + j + 1\<close> show ?thesis
        by(rule_tac x="Suc i" in exI) auto
    qed
  qed
  with that show ?thesis by blast
qed


lemma while_red_nE:
  "\<langle>while (b) cx,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle> 
  \<Longrightarrow> (\<lbrakk>b\<rbrakk> s = Some false \<and> s = s' \<and> n = 1) \<or>
     (\<exists>i j s''. \<lbrakk>b\<rbrakk> s = Some true \<and> \<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle> \<and> 
                \<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle> \<and> n = i + j + 2)"
proof(induct "while (b) cx" s n "Skip" s' rule:red_n.induct)
  case (red_n_Rec s c'' s'' n s')
  from \<open>\<langle>while (b) cx,s\<rangle> \<rightarrow> \<langle>c'',s''\<rangle>\<close>
  have "(\<lbrakk>b\<rbrakk> s = Some false \<and> c'' = Skip \<and> s'' = s) \<or>
    (\<lbrakk>b\<rbrakk> s = Some true \<and> c'' = cx;;while (b) cx \<and> s'' = s)"
    by(induct "while (b) cx" _ _ _ rule:red_induct) auto
  thus ?case
  proof
    assume "\<lbrakk>b\<rbrakk> s = Some false \<and> c'' = Skip \<and> s'' = s"
    hence "\<lbrakk>b\<rbrakk> s = Some false" and "c'' = Skip" and "s'' = s" by simp_all
    with \<open>\<langle>c'',s''\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>\<close> have "s = s'" and "n = 0"
      by(induct _ _ Skip _ rule:red_n.induct,auto elim:red.cases)
    with \<open>\<lbrakk>b\<rbrakk> s = Some false\<close> show ?thesis by fastforce
  next
    assume "\<lbrakk>b\<rbrakk> s = Some true \<and> c'' = cx;;while (b) cx \<and> s'' = s"
    hence "\<lbrakk>b\<rbrakk> s = Some true" and "c'' = cx;;while (b) cx" 
      and "s'' = s" by simp_all
    with \<open>\<langle>c'',s''\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>\<close>
    obtain i j sx where "\<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,sx\<rangle>" and "\<langle>while (b) cx,sx\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>"
      and "n = i + j + 1" by(fastforce elim:Seq_red_nE)
    with \<open>\<lbrakk>b\<rbrakk> s = Some true\<close> show ?thesis by fastforce
  qed
qed


lemma while_red_n_induct [consumes 1, case_names false true]:
  assumes major: "\<langle>while (b) cx,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>"
  and IHfalse:"\<And>s.  \<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> P s s"
  and IHtrue:"\<And>s i j s''. \<lbrakk>  \<lbrakk>b\<rbrakk> s = Some true; \<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle>; 
                            \<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>; P s'' s'\<rbrakk> \<Longrightarrow> P s s'"
  shows "P s s'"
using major
proof(induct n arbitrary:s rule:nat_less_induct)
  fix n s
  assume IHall:"\<forall>m<n. \<forall>x. \<langle>while (b) cx,x\<rangle> \<rightarrow>\<^bsup>m\<^esup> \<langle>Skip,s'\<rangle> \<longrightarrow> P x s'"
    and  "\<langle>while (b) cx,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>"
  from \<open>\<langle>while (b) cx,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>Skip,s'\<rangle>\<close>
  have "(\<lbrakk>b\<rbrakk> s = Some false \<and> s = s' \<and> n = 1) \<or>
     (\<exists>i j s''. \<lbrakk>b\<rbrakk> s = Some true \<and> \<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle> \<and> 
                \<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle> \<and> n = i + j + 2)" 
    by(rule while_red_nE)
  thus "P s s'"
  proof
    assume "\<lbrakk>b\<rbrakk> s = Some false \<and> s = s' \<and> n = 1"
    hence "\<lbrakk>b\<rbrakk> s = Some false" and "s = s'" by auto
    from IHfalse[OF \<open>\<lbrakk>b\<rbrakk> s = Some false\<close>] have "P s s" .
    with \<open>s = s'\<close> show ?thesis by simp
  next
    assume "\<exists>i j s''. \<lbrakk>b\<rbrakk> s = Some true \<and> \<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle> \<and> 
                      \<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle> \<and> n = i + j + 2"
    then obtain i j s'' where "\<lbrakk>b\<rbrakk> s = Some true"
      and "\<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle>" and "\<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>"
      and "n = i + j + 2" by blast
    with IHall have "P s'' s'"
      apply(erule_tac x="j" in allE) apply clarsimp done
    from IHtrue[OF \<open>\<lbrakk>b\<rbrakk> s = Some true\<close> \<open>\<langle>cx,s\<rangle> \<rightarrow>\<^bsup>i\<^esup> \<langle>Skip,s''\<rangle>\<close> 
      \<open>\<langle>while (b) cx,s''\<rangle> \<rightarrow>\<^bsup>j\<^esup> \<langle>Skip,s'\<rangle>\<close> this] show ?thesis .
  qed
qed


lemma reds_to_red_n:"\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle> \<Longrightarrow> \<exists>n. \<langle>c,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>c',s'\<rangle>"
by(induct rule:converse_rtranclp_induct2,auto intro:red_n.intros)


lemma red_n_to_reds:"\<langle>c,s\<rangle> \<rightarrow>\<^bsup>n\<^esup> \<langle>c',s'\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>"
by(induct rule:red_n.induct,auto intro:converse_rtranclp_into_rtranclp)


lemma while_reds_induct[consumes 1, case_names false true]:
  "\<lbrakk>\<langle>while (b) cx,s\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>; \<And>s. \<lbrakk>b\<rbrakk> s = Some false \<Longrightarrow> P s s;
    \<And>s s''. \<lbrakk> \<lbrakk>b\<rbrakk> s = Some true; \<langle>cx,s\<rangle> \<rightarrow>* \<langle>Skip,s''\<rangle>; 
             \<langle>while (b) cx,s''\<rangle> \<rightarrow>* \<langle>Skip,s'\<rangle>; P s'' s'\<rbrakk> \<Longrightarrow> P s s'\<rbrakk>
  \<Longrightarrow> P s s'"
apply(drule reds_to_red_n,clarsimp)
apply(erule while_red_n_induct,clarsimp)
by(auto dest:red_n_to_reds)


lemma red_det:
  "\<lbrakk>\<langle>c,s\<rangle> \<rightarrow> \<langle>c\<^sub>1,s\<^sub>1\<rangle>; \<langle>c,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> c\<^sub>1 = c\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2"
proof(induct arbitrary:c\<^sub>2 rule:red_induct)
  case (SeqRed c\<^sub>1 s c\<^sub>1' s' c\<^sub>2')
  note IH = \<open>\<And>c\<^sub>2. \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<^sub>2\<rangle> \<Longrightarrow> c\<^sub>1' = c\<^sub>2 \<and> s' = s\<^sub>2\<close>
  from \<open>\<langle>c\<^sub>1;;c\<^sub>2',s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<^sub>2\<rangle>\<close> have "c\<^sub>1 = Skip \<or> (\<exists>cx. c\<^sub>2 = cx;;c\<^sub>2' \<and> \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>cx,s\<^sub>2\<rangle>)"
    by(fastforce elim:red.cases)
  thus ?case
  proof
    assume "c\<^sub>1 = Skip"
    with \<open>\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s'\<rangle>\<close> have False by(fastforce elim:red.cases)
    thus ?thesis by simp
  next
    assume "\<exists>cx. c\<^sub>2 = cx;;c\<^sub>2' \<and> \<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>cx,s\<^sub>2\<rangle>"
    then obtain cx where "c\<^sub>2 = cx;;c\<^sub>2'" and "\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>cx,s\<^sub>2\<rangle>" by blast
    from IH[OF \<open>\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>cx,s\<^sub>2\<rangle>\<close>] have "c\<^sub>1' = cx \<and> s' = s\<^sub>2" .
    with \<open>c\<^sub>2 = cx;;c\<^sub>2'\<close> show ?thesis by simp
  qed
qed (fastforce elim:red.cases)+


theorem reds_det:
  "\<lbrakk>\<langle>c,s\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>1\<rangle>; \<langle>c,s\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>2\<rangle>\<rbrakk> \<Longrightarrow> s\<^sub>1 = s\<^sub>2"
proof(induct rule:converse_rtranclp_induct2)
  case refl
  from \<open>\<langle>Skip,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>2\<rangle>\<close> show ?case
    by -(erule converse_rtranclpE,auto elim:red.cases)
next
  case (step c'' s'' c' s')
  note IH = \<open>\<langle>c',s'\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>2\<rangle> \<Longrightarrow> s\<^sub>1 = s\<^sub>2\<close>
  from step have "\<langle>c'',s''\<rangle> \<rightarrow> \<langle>c',s'\<rangle>"
    by simp
  from \<open>\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>2\<rangle>\<close> this have "\<langle>c',s'\<rangle> \<rightarrow>* \<langle>Skip,s\<^sub>2\<rangle>"
    by -(erule converse_rtranclpE,auto elim:red.cases dest:red_det)
  from IH[OF this] show ?thesis .
qed


end
