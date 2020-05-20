subsection\<open>SC to ND\<close>
theory SCND
imports SC ND
begin

lemma SCND: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> (set_mset \<Gamma>) \<union> Not ` (set_mset \<Delta>) \<turnstile> \<bottom>"
proof(induction \<Gamma> \<Delta> rule: SCp.induct)
  case BotL thus ?case by (simp add: ND.Ax)
next
  case Ax thus ?case by (meson ND.Ax NotE UnCI image_iff)
next
  case NotL thus ?case by (simp add: NotI)
next
  case (NotR F \<Gamma> \<Delta>) thus ?case by (simp add: Not2IE)
next
  case (AndL F G \<Gamma> \<Delta>) thus ?case by (simp add: AndL_sim)
next
  case (AndR \<Gamma> F \<Delta> G) thus ?case by(simp add: AndR_sim)
next
  case OrL thus ?case by (simp add: OrL_sim)
next
  case OrR thus ?case using OrR_sim[where 'a='a] by (simp add: insert_commute)
next
  case (ImpL \<Gamma> F \<Delta> G) from ImpL.IH show ?case by (simp add: ImpL_sim)
next
  case ImpR from ImpR.IH show ?case by (simp add: ImpR_sim)
qed

end
