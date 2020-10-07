(*  Title:       POSIX Lexing with Derivatives of Regular Expressions
    Authors:     Fahad Ausaf <fahad.ausaf at icloud.com>, 2016
                 Roy Dyckhoff <roy.dyckhoff at st-andrews.ac.uk>, 2016
                 Christian Urban <christian.urban at kcl.ac.uk>, 2016
    Maintainer:  Christian Urban <christian.urban at kcl.ac.uk>
*) 

theory Simplifying
  imports Lexer 
begin

section \<open>Lexer including simplifications\<close>


fun F_RIGHT where
  "F_RIGHT f v = Right (f v)"

fun F_LEFT where
  "F_LEFT f v = Left (f v)"

fun F_Plus where
  "F_Plus f\<^sub>1 f\<^sub>2 (Right v) = Right (f\<^sub>2 v)"
| "F_Plus f\<^sub>1 f\<^sub>2 (Left v) = Left (f\<^sub>1 v)"  
| "F_Plus f1 f2 v = v"


fun F_Times1 where
  "F_Times1 f\<^sub>1 f\<^sub>2 v = Seq (f\<^sub>1 Void) (f\<^sub>2 v)"

fun F_Times2 where 
  "F_Times2 f\<^sub>1 f\<^sub>2 v = Seq (f\<^sub>1 v) (f\<^sub>2 Void)"

fun F_Times where 
  "F_Times f\<^sub>1 f\<^sub>2 (Seq v\<^sub>1 v\<^sub>2) = Seq (f\<^sub>1 v\<^sub>1) (f\<^sub>2 v\<^sub>2)"
| "F_Times f1 f2 v = v"

fun simp_Plus where
  "simp_Plus (Zero, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (r\<^sub>2, F_RIGHT f\<^sub>2)"
| "simp_Plus (r\<^sub>1, f\<^sub>1) (Zero, f\<^sub>2) = (r\<^sub>1, F_LEFT f\<^sub>1)"
| "simp_Plus (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (Plus r\<^sub>1 r\<^sub>2, F_Plus f\<^sub>1 f\<^sub>2)"

fun simp_Times where
  "simp_Times (One, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (r\<^sub>2, F_Times1 f\<^sub>1 f\<^sub>2)"
| "simp_Times (r\<^sub>1, f\<^sub>1) (One, f\<^sub>2) = (r\<^sub>1, F_Times2 f\<^sub>1 f\<^sub>2)"
| "simp_Times (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (Times r\<^sub>1 r\<^sub>2, F_Times f\<^sub>1 f\<^sub>2)"  
 
lemma simp_Times_simps[simp]:
  "simp_Times p1 p2 = (if (fst p1 = One) then (fst p2, F_Times1 (snd p1) (snd p2))
                    else (if (fst p2 = One) then (fst p1, F_Times2 (snd p1) (snd p2))
                    else (Times (fst p1) (fst p2), F_Times (snd p1) (snd p2))))"
by (induct p1 p2 rule: simp_Times.induct) (auto)

lemma simp_Plus_simps[simp]:
  "simp_Plus p1 p2 = (if (fst p1 = Zero) then (fst p2, F_RIGHT (snd p2))
                    else (if (fst p2 = Zero) then (fst p1, F_LEFT (snd p1))
                    else (Plus (fst p1) (fst p2), F_Plus (snd p1) (snd p2))))"
by (induct p1 p2 rule: simp_Plus.induct) (auto)

fun 
  simp :: "'a rexp \<Rightarrow> 'a rexp * ('a val \<Rightarrow> 'a val)"
where
  "simp (Plus r1 r2) = simp_Plus (simp r1) (simp r2)" 
| "simp (Times r1 r2) = simp_Times (simp r1) (simp r2)" 
| "simp r = (r, id)"

fun 
  slexer :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> ('a val) option"
where
  "slexer r [] = (if nullable r then Some(mkeps r) else None)"
| "slexer r (c#s) = (let (rs, fr) = simp (deriv c r) in
                         (case (slexer rs s) of  
                            None \<Rightarrow> None
                          | Some(v) \<Rightarrow> Some(injval r c (fr v))))"

lemma slexer_better_simp:
  "slexer r (c#s) = (case (slexer (fst (simp (deriv c r))) s) of  
                            None \<Rightarrow> None
                          | Some(v) \<Rightarrow> Some(injval r c ((snd (simp (deriv c r))) v)))"
by (auto split: prod.split option.split)


lemma L_fst_simp:
  shows "lang r = lang (fst (simp r))"
by (induct r) (auto)

lemma Posix_simp:
  assumes "s \<in> (fst (simp r)) \<rightarrow> v" 
  shows "s \<in> r \<rightarrow> ((snd (simp r)) v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case (Plus r1 r2 s v)
  have IH1: "\<And>s v. s \<in> fst (simp r1) \<rightarrow> v \<Longrightarrow> s \<in> r1 \<rightarrow> snd (simp r1) v" by fact
  have IH2: "\<And>s v. s \<in> fst (simp r2) \<rightarrow> v \<Longrightarrow> s \<in> r2 \<rightarrow> snd (simp r2) v" by fact
  have as: "s \<in> fst (simp (Plus r1 r2)) \<rightarrow> v" by fact
  consider (Zero_Zero) "fst (simp r1) = Zero" "fst (simp r2) = Zero"
         | (Zero_NZero) "fst (simp r1) = Zero" "fst (simp r2) \<noteq> Zero"
         | (NZero_Zero) "fst (simp r1) \<noteq> Zero" "fst (simp r2) = Zero"
         | (NZero_NZero) "fst (simp r1) \<noteq> Zero" "fst (simp r2) \<noteq> Zero" by auto
  then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v" 
    proof(cases)
      case (Zero_Zero)
      with as have "s \<in> Zero \<rightarrow> v" by simp 
      then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v" by (rule Posix_elims(1))
    next
      case (Zero_NZero)
      with as have "s \<in> fst (simp r2) \<rightarrow> v" by simp
      with IH2 have "s \<in> r2 \<rightarrow> snd (simp r2) v" by simp
      moreover
      from Zero_NZero have "fst (simp r1) = Zero" by simp
      then have "lang (fst (simp r1)) = {}" by simp
      then have "lang r1 = {}" using L_fst_simp by auto
      then have "s \<notin> lang r1" by simp 
      ultimately have "s \<in> Plus r1 r2 \<rightarrow> Right (snd (simp r2) v)" by (rule Posix_Plus2)
      then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v"
      using Zero_NZero by simp
    next
      case (NZero_Zero)
      with as have "s \<in> fst (simp r1) \<rightarrow> v" by simp
      with IH1 have "s \<in> r1 \<rightarrow> snd (simp r1) v" by simp
      then have "s \<in> Plus r1 r2 \<rightarrow> Left (snd (simp r1) v)" by (rule Posix_Plus1) 
      then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v" using NZero_Zero by simp
    next
      case (NZero_NZero)
      with as have "s \<in> Plus (fst (simp r1)) (fst (simp r2)) \<rightarrow> v" by simp
      then consider (Left) v1 where "v = Left v1" "s \<in> (fst (simp r1)) \<rightarrow> v1"
                  | (Right) v2 where "v = Right v2" "s \<in> (fst (simp r2)) \<rightarrow> v2" "s \<notin> lang (fst (simp r1))"
                  by (erule_tac Posix_elims(4)) 
      then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v"
      proof(cases)
        case (Left)
        then have "v = Left v1" "s \<in> r1 \<rightarrow> (snd (simp r1) v1)" using IH1 by simp_all
        then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v" using NZero_NZero
          by (simp_all add: Posix_Plus1)
      next 
        case (Right)
        then have "v = Right v2" "s \<in> r2 \<rightarrow> (snd (simp r2) v2)" "s \<notin> lang r1" using IH2 L_fst_simp by auto
        then show "s \<in> Plus r1 r2 \<rightarrow> snd (simp (Plus r1 r2)) v" using NZero_NZero
          by (simp_all add: Posix_Plus2)
      qed
    qed
next
  case (Times r1 r2 s v)
  have IH1: "\<And>s v. s \<in> fst (simp r1) \<rightarrow> v \<Longrightarrow> s \<in> r1 \<rightarrow> snd (simp r1) v" by fact
  have IH2: "\<And>s v. s \<in> fst (simp r2) \<rightarrow> v \<Longrightarrow> s \<in> r2 \<rightarrow> snd (simp r2) v" by fact
  have as: "s \<in> fst (simp (Times r1 r2)) \<rightarrow> v" by fact
  consider (One_One) "fst (simp r1) = One" "fst (simp r2) = One"
         | (One_NOne) "fst (simp r1) = One" "fst (simp r2) \<noteq> One"
         | (NOne_One) "fst (simp r1) \<noteq> One" "fst (simp r2) = One"
         | (NOne_NOne) "fst (simp r1) \<noteq> One" "fst (simp r2) \<noteq> One" by auto
  then show "s \<in> Times r1 r2 \<rightarrow> snd (simp (Times r1 r2)) v" 
  proof(cases)
      case (One_One)
      with as have b: "s \<in> One \<rightarrow> v" by simp 
      from b have "s \<in> r1 \<rightarrow> snd (simp r1) v" using IH1 One_One by simp
      moreover
      from b have c: "s = []" "v = Void" using Posix_elims(2) by auto
      moreover
      have "[] \<in> One \<rightarrow> Void" by (simp add: Posix_One)
      then have "[] \<in> fst (simp r2) \<rightarrow> Void" using One_One by simp
      then have "[] \<in> r2 \<rightarrow> snd (simp r2) Void" using IH2 by simp
      ultimately have "([] @ []) \<in> Times r1 r2 \<rightarrow> Seq (snd (simp r1) Void) (snd (simp r2) Void)"
        using Posix_Times by blast 
      then show "s \<in> Times r1 r2 \<rightarrow> snd (simp (Times r1 r2)) v" using c One_One by simp
    next
      case (One_NOne)
      with as have b: "s \<in> fst (simp r2) \<rightarrow> v" by simp 
      from b have "s \<in> r2 \<rightarrow> snd (simp r2) v" using IH2 One_NOne by simp
      moreover
      have "[] \<in> One \<rightarrow> Void" by (simp add: Posix_One)
      then have "[] \<in> fst (simp r1) \<rightarrow> Void" using One_NOne by simp
      then have "[] \<in> r1 \<rightarrow> snd (simp r1) Void" using IH1 by simp
      moreover
      from One_NOne(1) have "lang (fst (simp r1)) = {[]}" by simp
      then have "lang r1 = {[]}" by (simp add: L_fst_simp[symmetric])
      ultimately have "([] @ s) \<in> Times r1 r2 \<rightarrow> Seq (snd (simp r1) Void) (snd (simp r2) v)"
        by(rule_tac Posix_Times) auto
      then show "s \<in> Times r1 r2 \<rightarrow> snd (simp (Times r1 r2)) v" using One_NOne by simp
    next
      case (NOne_One)
        with as have "s \<in> fst (simp r1) \<rightarrow> v" by simp
        with IH1 have "s \<in> r1 \<rightarrow> snd (simp r1) v" by simp
      moreover
        have "[] \<in> One \<rightarrow> Void" by (simp add: Posix_One)
        then have "[] \<in> fst (simp r2) \<rightarrow> Void" using NOne_One by simp
        then have "[] \<in> r2 \<rightarrow> snd (simp r2) Void" using IH2 by simp
      ultimately have "(s @ []) \<in> Times r1 r2 \<rightarrow> Seq (snd (simp r1) v) (snd (simp r2) Void)"
        by(rule_tac Posix_Times) auto
      then show "s \<in> Times r1 r2 \<rightarrow> snd (simp (Times r1 r2)) v" using NOne_One by simp
    next
      case (NOne_NOne)
      with as have "s \<in> Times (fst (simp r1)) (fst (simp r2)) \<rightarrow> v" by simp
      then obtain s1 s2 v1 v2 where eqs: "s = s1 @ s2" "v = Seq v1 v2"
                     "s1 \<in> (fst (simp r1)) \<rightarrow> v1" "s2 \<in> (fst (simp r2)) \<rightarrow> v2"
                     "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)"
                     by (erule_tac Posix_elims(5)) (auto simp add: L_fst_simp[symmetric]) 
      then have "s1 \<in> r1 \<rightarrow> (snd (simp r1) v1)" "s2 \<in> r2 \<rightarrow> (snd (simp r2) v2)"
        using IH1 IH2 by auto             
      then show "s \<in> Times r1 r2 \<rightarrow> snd (simp (Times r1 r2)) v" using eqs NOne_NOne
        by(auto intro: Posix_Times)
    qed
qed (simp_all)


lemma slexer_correctness:
  shows "slexer r s = lexer r s"
proof(induct s arbitrary: r)
  case Nil
  show "slexer r [] = lexer r []" by simp
next 
  case (Cons c s r)
  have IH: "\<And>r. slexer r s = lexer r s" by fact
  show "slexer r (c # s) = lexer r (c # s)" 
   proof (cases "s \<in> lang (deriv c r)")
     case True
       assume a1: "s \<in> lang (deriv c r)"
       then obtain v1 where a2: "lexer (deriv c r) s = Some v1" "s \<in> deriv c r \<rightarrow> v1"
         using lexer_correct_Some by auto
       from a1 have "s \<in> lang (fst (simp (deriv c r)))" using L_fst_simp[symmetric] by auto
       then obtain v2 where a3: "lexer (fst (simp (deriv c r))) s = Some v2" "s \<in> (fst (simp (deriv c r))) \<rightarrow> v2"
          using lexer_correct_Some by auto
       then have a4: "slexer (fst (simp (deriv c r))) s = Some v2" using IH by simp
       from a3(2) have "s \<in> deriv c r \<rightarrow> (snd (simp (deriv c r))) v2" using Posix_simp by auto
       with a2(2) have "v1 = (snd (simp (deriv c r))) v2" using Posix_determ by auto
       with a2(1) a4 show "slexer r (c # s) = lexer r (c # s)" by (auto split: prod.split)
     next 
     case False
       assume b1: "s \<notin> lang (deriv c r)"
       then have "lexer (deriv c r) s = None" using lexer_correct_None by auto
       moreover
       from b1 have "s \<notin> lang (fst (simp (deriv c r)))" using L_fst_simp[symmetric] by auto
       then have "lexer (fst (simp (deriv c r))) s = None" using lexer_correct_None by auto
       then have "slexer (fst (simp (deriv c r))) s = None" using IH by simp
       ultimately show "slexer r (c # s) = lexer r (c # s)" 
         by (simp del: slexer.simps add: slexer_better_simp)
   qed
qed  

end
