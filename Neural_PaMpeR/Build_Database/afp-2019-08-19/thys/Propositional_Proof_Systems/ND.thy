subsection\<open>Natural Deduction\<close>

theory ND
imports Formulas
begin

inductive ND :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<turnstile>" 30) where
Ax: "F \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> F" |
NotE: "\<lbrakk>\<Gamma> \<turnstile> Not F; \<Gamma> \<turnstile> F \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<bottom>" |
NotI: "F \<triangleright> \<Gamma> \<turnstile> \<bottom> \<Longrightarrow> \<Gamma> \<turnstile> Not F" |
CC: "Not F\<triangleright> \<Gamma> \<turnstile> \<bottom> \<Longrightarrow> \<Gamma> \<turnstile> F" |
AndE1: "\<Gamma> \<turnstile> And F G \<Longrightarrow> \<Gamma> \<turnstile> F" |
AndE2: "\<Gamma> \<turnstile> And F G \<Longrightarrow> \<Gamma> \<turnstile> G" |
AndI: "\<lbrakk> \<Gamma> \<turnstile> F; \<Gamma> \<turnstile> G \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> And F G" |
OrI1: "\<Gamma> \<turnstile> F \<Longrightarrow> \<Gamma> \<turnstile> Or F G" |
OrI2: "\<Gamma> \<turnstile> G \<Longrightarrow> \<Gamma> \<turnstile> Or F G" |
OrE: "\<lbrakk> \<Gamma> \<turnstile> Or F G; F\<triangleright>\<Gamma> \<turnstile> H; G\<triangleright>\<Gamma> \<turnstile> H \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> H" |
ImpI: "F \<triangleright> \<Gamma> \<turnstile> G \<Longrightarrow> \<Gamma> \<turnstile> Imp F G" |
ImpE: "\<lbrakk> \<Gamma> \<turnstile> Imp F G; \<Gamma> \<turnstile> F \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> G"

(* Note that this is not a positive inductive definition because the
predicate occurs negatively in many rules:
inductive ND :: "form \<Rightarrow> bool" ("\<turnstile> _" [30] 30) where
NotE: "\<lbrakk>\<turnstile> Not F; \<turnstile> F \<rbrakk> \<Longrightarrow> \<turnstile> \<bottom>" |
NotI: "\<lbrakk>\<turnstile> F \<Longrightarrow> \<turnstile> \<bottom>\<rbrakk> \<Longrightarrow> \<turnstile> Not F" |
CC: "\<lbrakk>\<turnstile> Not F \<Longrightarrow> \<turnstile> \<bottom>\<rbrakk> \<Longrightarrow> \<turnstile> F" |
AndE1: "\<turnstile> And F G \<Longrightarrow> \<turnstile> F" |
AndE2: "\<turnstile> And F G \<Longrightarrow> \<turnstile> G" |
AndI: "\<lbrakk> \<turnstile> F; \<turnstile> G \<rbrakk> \<Longrightarrow> \<turnstile> And F G" |
OrI1: "\<turnstile> F \<Longrightarrow> \<turnstile> Or F G" |
OrI2: "\<turnstile> G \<Longrightarrow> \<turnstile> Or F G" |
OrE: "\<lbrakk> \<turnstile> Or F G; \<turnstile> F \<Longrightarrow> \<turnstile> H; \<turnstile> G \<Longrightarrow> \<turnstile> H \<rbrakk> \<Longrightarrow> \<turnstile> H" |
ImpI: "\<lbrakk>\<turnstile> F \<Longrightarrow> \<turnstile> G\<rbrakk> \<Longrightarrow> \<turnstile> Imp F G" |
ImpE: "\<lbrakk> \<turnstile> Imp F G; \<turnstile> F \<rbrakk> \<Longrightarrow> \<turnstile> G"
*)

lemma Weaken: "\<lbrakk> \<Gamma> \<turnstile> F; \<Gamma> \<subseteq> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> F"
proof(induct arbitrary: \<Gamma>' rule: ND.induct)
  case (NotI F \<Gamma>) thus ?case using ND.NotI by auto
next
  case Ax thus ?case by(blast intro: ND.Ax)
next
  case NotE thus ?case by(blast intro: ND.NotE)
next
  case CC thus ?case using ND.CC by blast
next
  case AndE1 thus ?case using ND.AndE1 by metis
next
  case AndE2 thus ?case using ND.AndE2 by metis
next
  case AndI thus ?case by (simp add: ND.AndI)
next
  case OrI1 thus ?case using ND.OrI1 by blast
next
  case OrI2 thus ?case using ND.OrI2 by blast
next
  case (OrE \<Gamma> F G H) show ?case apply(insert OrE.prems)
    apply(rule ND.OrE[of \<Gamma>' F G]) 
      apply(rule OrE.hyps(2)[OF OrE.prems]) 
     apply(rule OrE.hyps(4); blast)
    apply(rule OrE.hyps(6); blast)
  done
next
  case ImpI thus ?case using ND.ImpI by blast
next
  case ImpE thus ?case using ND.ImpE by metis
qed

lemma BotE (* ex falso *): "\<Gamma> \<turnstile> \<bottom> \<Longrightarrow> \<Gamma> \<turnstile> F"
  by (meson CC subset_insertI Weaken)

lemma Not2E: "Not(Not F)\<triangleright> \<Gamma> \<turnstile> F"
  by (metis CC ND.Ax NotE insertI1 insert_commute)

lemma Not2I: "F\<triangleright>\<Gamma> \<turnstile> Not(Not F)"
  by (metis CC ND.Ax NotE insertI1 insert_commute)

lemma Not2IE: "F\<triangleright>\<Gamma> \<turnstile> G \<Longrightarrow> Not (Not F)\<triangleright> \<Gamma> \<turnstile> G"
  by (meson ImpE ImpI Not2E Weaken subset_insertI)

lemma NDtrans: "\<Gamma> \<turnstile> F \<Longrightarrow> F\<triangleright> \<Gamma> \<turnstile> G \<Longrightarrow> \<Gamma> \<turnstile> G"
  using ImpE ImpI by blast

lemma AndL_sim: "F \<triangleright> G \<triangleright> \<Gamma> \<turnstile> H \<Longrightarrow> And F G \<triangleright> \<Gamma> \<turnstile> H"
  apply(drule Weaken[where \<Gamma>' = "And F G \<triangleright> F \<triangleright> G \<triangleright> \<Gamma>"])
   apply blast
by (metis AndE1 AndE2 ND.Ax NDtrans insertI1 insert_commute)

lemma NotSwap: "Not F\<triangleright> \<Gamma> \<turnstile> G \<Longrightarrow> Not G\<triangleright> \<Gamma> \<turnstile> F"
  using CC NotE insert_commute subset_insertI Weaken by (metis Ax insertI1)
lemma AndR_sim: "\<lbrakk> Not F\<triangleright> \<Gamma> \<turnstile> H; Not G\<triangleright> \<Gamma> \<turnstile> H \<rbrakk> \<Longrightarrow> Not(And F G)\<triangleright> \<Gamma> \<turnstile> H"
  using AndI NotSwap by blast

lemma OrL_sim: "\<lbrakk> F\<triangleright> \<Gamma> \<turnstile> H; G\<triangleright>\<Gamma> \<turnstile> H \<rbrakk> \<Longrightarrow> F \<^bold>\<or> G\<triangleright> \<Gamma> \<turnstile> H"
  using Weaken[where \<Gamma>' = "F\<triangleright> Or F G\<triangleright> \<Gamma>"] Weaken[where \<Gamma>' = "G\<triangleright> Or F G\<triangleright> \<Gamma>"]
  by (meson ND.Ax OrE insertI1 insert_mono subset_insertI)

lemma OrR_sim: "\<lbrakk> \<^bold>\<not> F\<triangleright> \<^bold>\<not> G\<triangleright> \<Gamma> \<turnstile> \<bottom>\<rbrakk> \<Longrightarrow> \<^bold>\<not> (G \<^bold>\<or> F)\<triangleright> \<Gamma> \<turnstile> \<bottom>"
proof -
  assume "\<^bold>\<not> F \<triangleright> \<^bold>\<not> G \<triangleright> \<Gamma> \<turnstile> \<bottom>"
  then have "\<And>f. f \<triangleright> \<^bold>\<not> F \<triangleright> \<^bold>\<not> G \<triangleright> \<Gamma> \<turnstile> \<bottom>" by (meson Weaken subset_insertI)
  then have "\<And>f. \<^bold>\<not> G \<triangleright> \<^bold>\<not> (f \<^bold>\<or> F) \<triangleright> \<Gamma> \<turnstile> \<bottom>" by (metis NDtrans Not2E NotSwap OrI2 insert_commute)
  then show ?thesis by (meson NDtrans Not2I NotSwap OrI1)
qed

lemma ImpL_sim: "\<lbrakk> \<^bold>\<not> F\<triangleright> \<Gamma> \<turnstile> \<bottom>; G\<triangleright> \<Gamma> \<turnstile> \<bottom>\<rbrakk> \<Longrightarrow> F \<^bold>\<rightarrow> G\<triangleright> \<Gamma> \<turnstile> \<bottom>"
  by (meson CC ImpE ImpI ND.Ax Weaken insertI1 subset_insertI)

lemma ImpR_sim: "\<lbrakk> \<^bold>\<not> G\<triangleright> F\<triangleright> \<Gamma> \<turnstile> \<bottom>\<rbrakk> \<Longrightarrow> \<^bold>\<not> (F \<^bold>\<rightarrow> G)\<triangleright> \<Gamma> \<turnstile> \<bottom>"
  by (metis (full_types) ImpI NotSwap insert_commute)

lemma ND_lem: "{} \<turnstile> Not F \<^bold>\<or> F"
  apply(rule CC)
  apply(rule OrE[of _ "Not F" F])
    apply(rule OrI1)
    apply(rule NotI)
    apply(rule NotE[of _ "(\<^bold>\<not> F \<^bold>\<or> F)"]; blast intro: OrI1 OrI2 Ax)+
done

lemma ND_caseDistinction: "\<lbrakk> F\<triangleright>\<Gamma> \<turnstile> H; Not F\<triangleright>\<Gamma> \<turnstile> H \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> H"
  by (meson ND_lem OrE empty_subsetI Weaken)

lemma "\<lbrakk>\<^bold>\<not> F\<triangleright> \<Gamma> \<turnstile> H; G\<triangleright> \<Gamma> \<turnstile> H\<rbrakk> \<Longrightarrow> F \<^bold>\<rightarrow> G\<triangleright> \<Gamma> \<turnstile> H"
  apply(rule ND_caseDistinction[of F])
   apply (meson ImpE ImpI ND.intros(1) Weaken insertI1 subset_insertI)
  apply (metis Weaken insert_commute subset_insertI)
done

lemma ND_deMorganAnd: "{\<^bold>\<not> (F \<^bold>\<and> G)} \<turnstile> \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G"
  apply(rule CC)
  apply(rule NotE[of _ "F \<^bold>\<and> G"])
   apply(simp add: Ax; fail)
  apply(rule AndI)
   apply(rule CC)
   apply(rule NotE[of _ "\<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G"])
    apply(simp add: Ax; fail)
   apply(rule OrI1)
   apply(simp add: Ax; fail)
  apply(rule CC)
   apply(rule NotE[of _ "\<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G"])
   apply(simp add: Ax; fail)
  apply(rule OrI2)
  apply(simp add: Ax; fail)
done

lemma ND_deMorganOr: "{\<^bold>\<not> (F \<^bold>\<or> G)} \<turnstile> \<^bold>\<not> F \<^bold>\<and> \<^bold>\<not> G" 
  apply(rule ND_caseDistinction[of F]; rule ND_caseDistinction[of G])
     apply(rule CC; rule NotE[of _ "F \<^bold>\<or> G"]; simp add: Ax OrI2 OrI1; fail)+
  apply(rule AndI; simp add: Ax; fail)
done

lemma sim_sim: "F\<triangleright> \<Gamma> \<turnstile> H \<Longrightarrow> G\<triangleright>\<Gamma> \<turnstile> F \<Longrightarrow> G\<triangleright> \<Gamma> \<turnstile> H"
  by (meson ImpE ImpI Weaken subset_insertI)
thm sim_sim[where \<Gamma>="{}", rotated, no_vars] (* a bit easier to read? *)
  
lemma Top_provable[simp,intro!]: "\<Gamma> \<turnstile> \<top>" unfolding Top_def by (intro ND.ImpI ND.Ax) simp

lemma NotBot_provable[simp,intro!]: "\<Gamma> \<turnstile> \<^bold>\<not> \<bottom>" using NotI BotE Ax by blast

lemma Top_useless: "\<Gamma> \<turnstile> F \<Longrightarrow> \<Gamma> - {\<top>} \<turnstile> F"
  by (metis NDtrans Top_provable Weaken insert_Diff_single subset_insertI)  

lemma AssmBigAnd: "set G \<turnstile> F \<longleftrightarrow> {} \<turnstile> (\<^bold>\<And>G \<^bold>\<rightarrow> F)"
 proof(induction G arbitrary: F)
    case Nil thus ?case by(fastforce intro: ND.ImpI elim: Weaken ImpE[OF _ NotBot_provable])
  next
    case (Cons G GS) show ?case proof
      assume "set (G # GS) \<turnstile> F"
      hence "set GS \<turnstile> G \<^bold>\<rightarrow> F" by(intro ND.ImpI) simp
      with Cons.IH have *: "{} \<turnstile> \<^bold>\<And> GS \<^bold>\<rightarrow> G \<^bold>\<rightarrow> F" ..
      hence "{G,\<^bold>\<And>GS} \<turnstile> F" proof -
        have *: "{\<^bold>\<And>GS} \<turnstile> G \<^bold>\<rightarrow> F" 
          using Weaken[OF * empty_subsetI] ImpE[where \<Gamma>="{\<^bold>\<And> GS}" and F="\<^bold>\<And> GS"] by (simp add: ND.Ax)
        show "{G,\<^bold>\<And>GS} \<turnstile> F" using Weaken[OF *] ImpE[where \<Gamma>="{G,\<^bold>\<And> GS}" and F="G"] ND.Ax by (simp add: ND.Ax)
      qed
      thus "{} \<turnstile> \<^bold>\<And> (G # GS) \<^bold>\<rightarrow> F" by(intro ND.ImpI; simp add: AndL_sim)
    next
      assume "{} \<turnstile> \<^bold>\<And> (G # GS) \<^bold>\<rightarrow> F"
      hence "{G \<^bold>\<and> \<^bold>\<And>GS} \<turnstile> F" using ImpE[OF _ Ax[OF singletonI]] Weaken by fastforce      
      hence "{G,\<^bold>\<And>GS} \<turnstile> F" by (meson AndI ImpE ImpI ND.intros(1) Weaken insertI1 subset_insertI)
      hence "{\<^bold>\<And>GS} \<turnstile> G \<^bold>\<rightarrow> F" using ImpI by blast
      hence "{} \<turnstile> \<^bold>\<And> GS \<^bold>\<rightarrow> G \<^bold>\<rightarrow> F" using ImpI by blast
      with Cons.IH have "set GS \<turnstile> G \<^bold>\<rightarrow> F" ..
      thus "set (G # GS) \<turnstile> F" using ImpE Weaken by (metis Ax list.set_intros(1) set_subset_Cons)
  qed
qed

end
