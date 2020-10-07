(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Up_To_Technique
imports Strong_Security
begin

context Strong_Security
begin

\<comment> \<open>define d-bisimulation 'up to' union of strong d-Bisimulations\<close>
definition d_Bisimulation_Up_To_USdB :: 
"'d \<Rightarrow> 'com Bisimulation_type \<Rightarrow> bool"
where
"d_Bisimulation_Up_To_USdB d R \<equiv> 
  (sym R) \<and> (\<forall>(V,V') \<in> R. length V = length V') \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. \<forall>m1 m1' W m2.
  \<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle> \<and> (m1 =\<^bsub>d\<^esub> m1')
  \<longrightarrow> (\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> 
    \<and> (W,W') \<in> (R \<union> (\<approx>\<^bsub>d\<^esub>)) \<and> (m2 =\<^bsub>d\<^esub> m2')))" 

lemma UpTo_aux: "\<And>V V' m1 m1' m2 W i. \<lbrakk> d_Bisimulation_Up_To_USdB d R;
  i < length V; (V,V') \<in> R; \<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>; m1 =\<^bsub>d\<^esub> m1' \<rbrakk>
  \<Longrightarrow> (\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> 
  \<and> (W,W') \<in> (R \<union> (\<approx>\<^bsub>d\<^esub>)) \<and> (m2 =\<^bsub>d\<^esub> m2'))"
  by (simp add: d_Bisimulation_Up_To_USdB_def, fastforce)

lemma RuUSdBeqlen: 
"\<lbrakk> d_Bisimulation_Up_To_USdB d R; 
  (V,V') \<in> (R \<union> (\<approx>\<^bsub>d\<^esub>)) \<rbrakk>
  \<Longrightarrow> length V = length V'"
by (auto, simp add: d_Bisimulation_Up_To_USdB_def, auto, 
  rule USdBeqlen, auto)

lemma Up_To_Technique: 
  assumes upToR: "d_Bisimulation_Up_To_USdB d R"
  shows "R \<subseteq> \<approx>\<^bsub>d\<^esub>"
proof -
  define S where "S = R \<union> (\<approx>\<^bsub>d\<^esub>)"
  from S_def have "R \<subseteq> S"
    by auto
  moreover 
  have "S \<subseteq> (\<approx>\<^bsub>d\<^esub>)"
  proof (simp add: USdB_def, auto, rule_tac x="S" in exI, auto,
      simp add: Strong_d_Bisimulation_def, auto)
      \<comment> \<open>show symmetry\<close>
    show symS: "sym S" 
    proof -
      from upToR
      have Rsym: "sym R"
        by (simp add: d_Bisimulation_Up_To_USdB_def)
      with USdBsym have Usym: 
        "sym (R \<union> (\<approx>\<^bsub>d\<^esub>))"
        by (metis sym_Un)
      with S_def show ?thesis
        by simp
    qed
  next 
    fix V V'
    assume inS: "(V,V') \<in> S" 
      \<comment> \<open>show equal length (by definition)\<close>
    from inS S_def upToR RuUSdBeqlen
    show eqlen: "length V = length V'"             
      by simp
  next
      \<comment> \<open>show general bisimulation property\<close>
    fix V V' W m1 m1' m2 i
    assume inS: "(V,V') \<in> S" 
    assume irange: "i < length V"
    assume stepV: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>" 
    assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
    
    from inS show "\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and>
      (W,W') \<in> S \<and> m2 =\<^bsub>d\<^esub> m2'"
    proof (simp add: S_def, auto)
      assume firstcase: "(V,V') \<in> R" 

      with upToR dequal irange stepV
        UpTo_aux[of "d" "R" "i" "V" "V'" "m1" "W" "m2" "m1'"]
      show "\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and>
        ((W,W') \<in> R \<or> W \<approx>\<^bsub>d\<^esub> W') \<and> m2 =\<^bsub>d\<^esub> m2'"
        by (auto simp add: S_def)
    next         
      assume secondcase: "V \<approx>\<^bsub>d\<^esub> V'"
      
      from USdB_Strong_d_Bisimulation upToR 
        secondcase dequal irange stepV
        strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i" "V" "V'" "m1" "W" "m2" "m1'"]
      show "\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and>
        ((W,W') \<in> R \<or> W \<approx>\<^bsub>d\<^esub> W') \<and> m2 =\<^bsub>d\<^esub> m2'"   
        by auto
    qed
  qed
                    
  ultimately show ?thesis by auto
qed

end

end
