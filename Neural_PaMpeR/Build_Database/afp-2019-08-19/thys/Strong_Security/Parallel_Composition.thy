(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Parallel_Composition
imports Up_To_Technique
begin

context Strong_Security
begin

theorem parallel_composition:
  assumes eqlen: "length V = length V'"
  assumes partsrelated: "\<forall>i < length V. [V!i] \<approx>\<^bsub>d\<^esub> [V'!i]"
  shows "V \<approx>\<^bsub>d\<^esub> V'"
proof -
  define R where "R = {(V,V'). length V = length V' 
    \<and> (\<forall>i < length V. [V!i] \<approx>\<^bsub>d\<^esub> [V'!i])}"
  from eqlen partsrelated have inR: "(V,V') \<in> R"
    by (simp add: R_def)
  
  have "d_Bisimulation_Up_To_USdB d R"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
      from USdBsym show "sym R" 
        by (simp add: R_def sym_def)
    next
      fix V V'
      assume "(V,V') \<in> R"
      with USdBeqlen show "length V = length V'" 
        by (simp add: R_def)
    next
      fix V V' i m1 m1' RS m2
      assume inR: "(V,V') \<in> R"
      assume irange: "i < length V"
      assume step: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>RS,m2\<rangle>"
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"

      from inR have Vassump:
        "length V = length V' \<and> (\<forall>i < length V. [V!i] \<approx>\<^bsub>d\<^esub> [V'!i])"
        by (simp add: R_def)

      with step dequal USdB_Strong_d_Bisimulation irange 
      strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "0" "[V!i]" "[V'!i]" "m1" "RS" "m2" "m1'"] 
      show "\<exists>RS' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
        ((RS,RS') \<in> R \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
        by (simp, fastforce)
    qed

    hence "R \<subseteq> (\<approx>\<^bsub>d\<^esub>)"
      by (rule Up_To_Technique)

    with inR show ?thesis by auto
qed



lemma parallel_decomposition:
  assumes related: "V \<approx>\<^bsub>d\<^esub> V'"
  shows "\<forall>i < length V. [V!i] \<approx>\<^bsub>d\<^esub> [V'!i]"
proof -
  define R where "R = {(C,C'). \<exists>i W W'. W \<approx>\<^bsub>d\<^esub> W' \<and> i < length W 
    \<and> C = [W!i] \<and> C' = [W'!i]}"

  with related have inR: "\<forall>i < length V. ([V!i],[V'!i]) \<in> R"
    by auto
  have "d_Bisimulation_Up_To_USdB d R"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
      from USdBsym USdBeqlen show "sym R"
        by (simp add: sym_def R_def, metis)
    next
      fix C C'
      assume "(C,C') \<in> R"
      with USdBeqlen show "length C = length C'" 
        by (simp add: R_def, auto)
    next
      fix C C' i m1 m1' RS m2
      assume inR: "(C,C') \<in> R"
      assume irange: "i < length C"
      assume step: "\<langle>C!i,m1\<rangle> \<rightarrow> \<langle>RS,m2\<rangle>"
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"

     from inR obtain j W W' where Rassump: 
       "W \<approx>\<^bsub>d\<^esub> W' \<and> j < length W \<and> C = [W!j] \<and> C' = [W'!j]"
       by (simp add: R_def, auto)

     with irange have i0: "i = 0" by auto

     from Rassump i0 strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "j" "W" "W'" 
       "m1" "RS" "m2" "m1'"] 
       USdB_Strong_d_Bisimulation step dequal
     show "\<exists>RS' m2'. \<langle>C'!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> 
       \<and> ((RS,RS') \<in> R \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
       by auto
   qed

   hence "R \<subseteq> (\<approx>\<^bsub>d\<^esub>)"
     by (rule Up_To_Technique)

   with inR show ?thesis
     by auto

qed

lemma USdB_comp_head_tail:
  assumes relatedhead: "[c] \<approx>\<^bsub>d\<^esub> [c']"
  assumes relatedtail: "V \<approx>\<^bsub>d\<^esub> V'"
  shows "(c#V) \<approx>\<^bsub>d\<^esub> (c'#V')"
proof -
  from relatedtail USdBeqlen have eqlen: "length (c#V) = length (c'#V')"
    by force
  
  from relatedtail parallel_decomposition have singleV: 
    "\<forall>i < length V. [V!i] \<approx>\<^bsub>d\<^esub> [V'!i]"
    by force

  with relatedhead have intermediate:
    "\<forall>i < length (c#V). [(c#V)!i] \<approx>\<^bsub>d\<^esub> [(c'#V')!i]"
    by (auto, case_tac i, auto)
      
  with eqlen parallel_composition
  show ?thesis
    by blast
qed
       
lemma USdB_decomp_head_tail:
  assumes relatedlist: "(c#V) \<approx>\<^bsub>d\<^esub> (c'#V')"
  shows "[c] \<approx>\<^bsub>d\<^esub> [c'] \<and> V \<approx>\<^bsub>d\<^esub> V'"
proof auto
  from relatedlist USdBeqlen[of "c#V" "c'#V'"] 
  have eqlen: "length V = length V'" 
    by auto
  
  from relatedlist parallel_decomposition[of "c#V" "c'#V'" "d"]
  have intermediate:
    "\<forall>i < length (c#V). [(c#V)!i] \<approx>\<^bsub>d\<^esub> [(c'#V')!i]"
    by auto
  thus "[c] \<approx>\<^bsub>d\<^esub> [c']"
    by force

  from intermediate eqlen show "V \<approx>\<^bsub>d\<^esub> V'"
  proof (case_tac V)
    assume Vcase1: "V = []"
    with eqlen have "V' = []" by auto
    with Vcase1 trivialpair_in_USdB show "V \<approx>\<^bsub>d\<^esub> V'" 
      by auto
  next
    fix c1 W
    assume Vcase2: "V = c1#W"
    hence Vlen: "length V > 0" by auto
    
    from intermediate have intermediate_aux:
      "\<And>i. i < length V
      \<Longrightarrow> [V!i] \<approx>\<^bsub>d\<^esub> [V'!i]"
      by force
    
    with parallel_composition[of "V" "V'"] eqlen
    show "V \<approx>\<^bsub>d\<^esub> V'"
      by blast
    
  qed
qed


end


end
