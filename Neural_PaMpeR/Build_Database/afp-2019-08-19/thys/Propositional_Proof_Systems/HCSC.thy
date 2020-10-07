section\<open>Proof Transformation\<close>
text\<open>This is organized as a ring closure\<close>
subsection\<open>HC to SC\<close>
theory HCSC
imports HC SC_Cut
begin

lemma extended_AxE[intro!]: "F, \<Gamma> \<Rightarrow> F, \<Delta>" by (intro extended_Ax) (simp add: add.commute inter_add_right2)

theorem HCSC: "AX10 \<union> set_mset \<Gamma> \<turnstile>\<^sub>H F \<Longrightarrow> \<Gamma> \<Rightarrow> {#F#}"
proof(induction rule: HC.induct)
  case (Ax F) thus ?case proof
    note SCp.intros(3-)[intro!]
    text\<open>Essentially, we need to prove all the axioms of Hibert Calculus in Sequent Calculus.\<close>
    have A: "\<Gamma> \<Rightarrow> {#F \<^bold>\<rightarrow> (F \<^bold>\<or> G)#}" for F G by blast
    have B: "\<Gamma> \<Rightarrow> {#G \<^bold>\<rightarrow> (F \<^bold>\<or> G)#}" for G F by blast
    have C: "\<Gamma> \<Rightarrow> {#(F \<^bold>\<rightarrow> H) \<^bold>\<rightarrow> ((G \<^bold>\<rightarrow> H) \<^bold>\<rightarrow> ((F \<^bold>\<or> G) \<^bold>\<rightarrow> H))#}" for F H G by blast
    have D: "\<Gamma> \<Rightarrow> {#(F \<^bold>\<and> G) \<^bold>\<rightarrow> F#}" for F G by blast
    have E: "\<Gamma> \<Rightarrow> {#(F \<^bold>\<and> G) \<^bold>\<rightarrow> G#}" for F G by blast
    have F: "\<Gamma> \<Rightarrow> {#F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> (F \<^bold>\<and> G))#}" for F G by blast
    have G: "\<Gamma> \<Rightarrow> {#(F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> \<^bold>\<not> F#}" for F by blast
    have H: "\<Gamma> \<Rightarrow> {#\<^bold>\<not> F \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> \<bottom>)#}" for F by blast
    have I: "\<Gamma> \<Rightarrow> {#(\<^bold>\<not> F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> F#}" for F  by blast
    have K: "\<Gamma> \<Rightarrow> {#F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> F)#}" for F G by blast
    have L: "\<Gamma> \<Rightarrow> {#(F \<^bold>\<rightarrow> (G \<^bold>\<rightarrow> H)) \<^bold>\<rightarrow> ((F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> (F \<^bold>\<rightarrow> H))#}" for F G H by blast
    have J: "F \<in> AX0 \<Longrightarrow> \<Gamma> \<Rightarrow> {#F#}" for F by(induction rule: AX0.induct; intro K L)
    assume "F \<in> AX10" thus ?thesis by(induction rule: AX10.induct; intro A B C D E F G H I J)
  next
    assume "F \<in> set_mset \<Gamma>" thus ?thesis by(intro extended_Ax) simp
  qed
next
  case (MP F G)
  from MP have IH: "\<Gamma> \<Rightarrow> {#F#}" "\<Gamma> \<Rightarrow> {#F \<^bold>\<rightarrow> G#}" by blast+
  with ImpR_inv[where \<Delta>=Mempty, simplified] have "F,\<Gamma> \<Rightarrow> {#G#}" by auto
  moreover from IH(1) weakenR have "\<Gamma> \<Rightarrow> F, {#G#}" by blast
  ultimately show "\<Gamma> \<Rightarrow> {#G#}" using cut[where F=F] by simp
qed

end
