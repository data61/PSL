(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Strong_Security
imports Types
begin

locale Strong_Security = 
fixes SR :: "('exp, 'id, 'val, 'com) TSteps"
and DA :: "('id, 'd::order) DomainAssignment"

begin

\<comment> \<open>define when two states are indistinguishable for an observer on domain d\<close>
definition d_equal :: "'d::order \<Rightarrow> ('id, 'val) State 
  \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"
where
"d_equal d m m' \<equiv> \<forall>x. ((DA x) \<le> d \<longrightarrow> (m x) = (m' x))"

abbreviation d_equal' :: "('id, 'val) State 
  \<Rightarrow> 'd::order \<Rightarrow> ('id, 'val) State \<Rightarrow> bool" 
( "(_ =\<^bsub>_\<^esub> _)" )
where
"m =\<^bsub>d\<^esub> m' \<equiv> d_equal d m m'"

\<comment> \<open>transitivity of d-equality\<close>
lemma d_equal_trans:
"\<lbrakk> m =\<^bsub>d\<^esub> m'; m' =\<^bsub>d\<^esub> m'' \<rbrakk> \<Longrightarrow> m =\<^bsub>d\<^esub> m''"
by (simp add: d_equal_def)


abbreviation SRabbr :: "('exp, 'id, 'val, 'com) TSteps_curry"
("(1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0] 81)
where
"\<langle>c,m\<rangle> \<rightarrow> \<langle>c',m'\<rangle> \<equiv> ((c,m),(c',m')) \<in> SR"

\<comment> \<open>predicate for strong d-bisimulation\<close>
definition Strong_d_Bisimulation :: "'d \<Rightarrow> 'com Bisimulation_type \<Rightarrow> bool"
where
"Strong_d_Bisimulation d R \<equiv> 
  (sym R) \<and>
  (\<forall>(V,V') \<in> R. length V = length V') \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. \<forall>m1 m1' m2 W.
  \<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle> \<and> m1 =\<^bsub>d\<^esub> m1'
  \<longrightarrow> (\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> (W,W') \<in> R \<and> m2 =\<^bsub>d\<^esub> m2'))"

\<comment> \<open>union of all strong d-bisimulations\<close>
definition USdB :: "'d \<Rightarrow> 'com Bisimulation_type"
("\<approx>\<^bsub>_\<^esub>" 65)
where
"\<approx>\<^bsub>d\<^esub> \<equiv> \<Union>{r. (Strong_d_Bisimulation d r)}"

abbreviation relatedbyUSdB :: "'com list \<Rightarrow> 'd \<Rightarrow> 'com list \<Rightarrow> bool" 
("(_ \<approx>\<^bsub>_\<^esub> _)" [66,66] 65)
where "V \<approx>\<^bsub>d\<^esub> V' \<equiv> (V,V') \<in> USdB d"

\<comment> \<open>predicate to define when a program is strongly secure\<close>
definition Strongly_Secure :: "'com list \<Rightarrow> bool"
where
"Strongly_Secure V \<equiv> (\<forall>d. V \<approx>\<^bsub>d\<^esub> V)"


\<comment> \<open>auxiliary lemma to obtain central strong d-Bisimulation property as Lemma
 in meta logic (allows instantiating all the variables manually if necessary)\<close>
lemma strongdB_aux: "\<And>V V' m1 m1' m2 W i. \<lbrakk> Strong_d_Bisimulation d R;
 i < length V ; (V,V') \<in> R; \<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>; m1 =\<^bsub>d\<^esub> m1' \<rbrakk>
 \<Longrightarrow> (\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> (W,W') \<in> R \<and> m2 =\<^bsub>d\<^esub> m2')"
by (simp add: Strong_d_Bisimulation_def, fastforce)

lemma trivialpair_in_USdB:
"[] \<approx>\<^bsub>d\<^esub> []"
by (simp add: USdB_def Strong_d_Bisimulation_def, 
  rule_tac x="{([],[])}" in exI, simp add: sym_def)

lemma USdBsym: "sym (\<approx>\<^bsub>d\<^esub>)"
by (simp add: USdB_def Strong_d_Bisimulation_def sym_def, auto)

lemma USdBeqlen: 
  "V \<approx>\<^bsub>d\<^esub> V' \<Longrightarrow> length V = length V'"
by (simp add: USdB_def Strong_d_Bisimulation_def, auto)              

lemma USdB_Strong_d_Bisimulation:
  "Strong_d_Bisimulation d (\<approx>\<^bsub>d\<^esub>)"
proof (simp add: Strong_d_Bisimulation_def, auto)
  show "sym (\<approx>\<^bsub>d\<^esub>)" by (rule USdBsym)
next
  fix V V'
  show "V \<approx>\<^bsub>d\<^esub> V' \<Longrightarrow> length V = length V'" by (rule USdBeqlen, auto)
next
  fix V V' m1 m1' m2 W i
  assume inUSdB: "V \<approx>\<^bsub>d\<^esub> V'"
  assume stepV: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>"
  assume irange: "i < length V"
  assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
  
  from inUSdB obtain R where someR:
    "Strong_d_Bisimulation d R \<and> (V,V') \<in> R" 
    by (simp add: USdB_def, auto)

  with strongdB_aux stepV irange dequal show 
    "\<exists>W' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> W \<approx>\<^bsub>d\<^esub> W' \<and> m2 =\<^bsub>d\<^esub> m2'"
    by (simp add: USdB_def, fastforce)
      
qed


lemma USdBtrans: "trans (\<approx>\<^bsub>d\<^esub>)"
proof (simp add: trans_def, auto)
  fix V V' V''
  assume p1: "V \<approx>\<^bsub>d\<^esub> V'"
  assume p2: "V' \<approx>\<^bsub>d\<^esub> V''"

  let ?R = "{(V,V''). \<exists>V'. V \<approx>\<^bsub>d\<^esub> V' \<and> V' \<approx>\<^bsub>d\<^esub> V''}"

  from p1 p2 have inRest: "(V,V'') \<in> ?R" by auto

  have SdB_rest: "Strong_d_Bisimulation d ?R"
    proof (simp add: Strong_d_Bisimulation_def sym_def, auto)
        fix V V' V''
        assume p1: "V \<approx>\<^bsub>d\<^esub> V'"
        moreover
        assume p2: "V' \<approx>\<^bsub>d\<^esub> V''"
        moreover
        from p1 USdBsym have "V' \<approx>\<^bsub>d\<^esub> V" 
          by (simp add: sym_def)
        moreover
        from p2 USdBsym have "V'' \<approx>\<^bsub>d\<^esub> V'" 
          by (simp add: sym_def)
        ultimately show  
        "\<exists>V'. V'' \<approx>\<^bsub>d\<^esub> V' \<and> V' \<approx>\<^bsub>d\<^esub> V"
          by (rule_tac x="V'" in exI, auto)
      next
        fix V V' V''
        assume p1: "V \<approx>\<^bsub>d\<^esub> V'"
        moreover
        assume p2: "V' \<approx>\<^bsub>d\<^esub> V''"
        moreover
        from p1 USdBeqlen[of "V" "V'"] have "length V = length V'"
          by auto
        moreover 
        from p2 USdBeqlen[of "V'" "V''"] have "length V' = length V''"
          by auto
        ultimately show eqlen: "length V = length V''" by auto
      next
        fix V V' V'' i m1 m1' W m2
        assume step: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>"
        assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
        assume p1: "V \<approx>\<^bsub>d\<^esub> V'"
        assume p2: "V' \<approx>\<^bsub>d\<^esub> V''"
        assume irange: "i < length V"
        from p1 USdBeqlen[of "V" "V'"] 
        have leq: "length V = length V'"
          by force
          
        have deq_same: "m1' =\<^bsub>d\<^esub> m1'" by (simp add: d_equal_def)

        from irange step dequal p1 USdB_Strong_d_Bisimulation 
          strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i" "V" "V'" "m1" "W" "m2" "m1'"]
        obtain W' m2' where p1concl: 
          "\<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> W \<approx>\<^bsub>d\<^esub> W' \<and> m2 =\<^bsub>d\<^esub> m2'"
          by auto
        
        with deq_same leq USdB_Strong_d_Bisimulation
          strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i" "V'" "V''" "m1'" "W'" "m2'" "m1'"]
          irange p2 dequal obtain W'' m2'' where p2concl:
          "W' \<approx>\<^bsub>d\<^esub> W'' \<and> \<langle>V''!i,m1'\<rangle> \<rightarrow> \<langle>W'',m2''\<rangle> \<and> m2' =\<^bsub>d\<^esub> m2''"
          by auto   

        from p1concl p2concl d_equal_trans have tt'': "m2 =\<^bsub>d\<^esub> m2''"
          by blast

        from p1concl p2concl have "(W,W'') \<in> ?R"
          by auto
        
        with p2concl tt'' show "\<exists>W'' m2''. \<langle>V''!i,m1'\<rangle> \<rightarrow> \<langle>W'',m2''\<rangle> \<and> 
          (\<exists>V'. W \<approx>\<^bsub>d\<^esub> V' \<and> V' \<approx>\<^bsub>d\<^esub> W'') \<and> m2 =\<^bsub>d\<^esub> m2''"
          by auto
    qed  

  hence liftup: "?R \<subseteq> (\<approx>\<^bsub>d\<^esub>)" 
    by (simp add: USdB_def, auto)

  with inRest show "V \<approx>\<^bsub>d\<^esub> V''"
    by auto

qed


end

end
