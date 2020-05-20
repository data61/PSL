(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
eqvt Rel
P \<leadsto>[Rel] Q

\<And>
\<Longrightarrow>

P \<sim> Q \<equiv> P \<leadsto>[\<sim>] Q \<and> Q \<leadsto>[\<sim>] P




lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes PBiSimQ: "P \<sim> Q"

  shows "<\<nu>x>P \<sim> <\<nu>x>Q"
proof -
  let ?X = "{x. \<exists>P Q. P \<sim> Q \<and> (\<exists>a. x = (<\<nu>a>P, <\<nu>a>Q))}"
  from PBiSimQ have "(<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by blast
  moreover have "\<And>P Q a. P \<leadsto>[bisim] Q \<Longrightarrow> <\<nu>a>P \<leadsto>[(?X \<union> bisim)] <\<nu>a>Q"
  proof -
    fix P Q a
    assume PSimQ: "P \<leadsto>[bisim] Q"
    moreover have "\<And>P Q a. P \<sim> Q \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> ?X \<union> bisim" by blast
    moreover have "bisim \<subseteq> ?X \<union> bisim" by blast
    moreover have "eqvt bisim" by(rule eqvt)
    moreover have "eqvt (?X \<union> bisim)"
      by(auto simp add: eqvt_def dest: eqvtI)+
    ultimately show "<\<nu>a>P \<leadsto>[(?X \<union> bisim)] <\<nu>a>Q"
      by(rule Strong_Late_Sim_Pres.resPres)
  qed
    
  ultimately show ?thesis using PBiSimQ
    by(coinduct, blast dest: unfoldE)
qed
