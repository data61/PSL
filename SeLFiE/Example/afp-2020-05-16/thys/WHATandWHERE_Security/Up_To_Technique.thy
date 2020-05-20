(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Up_To_Technique
imports WHATWHERE_Security
begin

context WHATWHERE
begin

abbreviation SdlHPPB where "SdlHPPB \<equiv> Strong_dlHPP_Bisimulation"

\<comment> \<open>define the 'reflexive part' of a relation (sets of elements which are related with themselves by the given relation)\<close>
definition Arefl :: "('a \<times> 'a) set \<Rightarrow> 'a set"
where
"Arefl R = {e. (e,e) \<in> R}"

lemma commonArefl_subset_commonDomain: 
"(Arefl R1 \<inter> Arefl R2) \<subseteq> (Domain R1 \<inter> Domain R2)"
  by (simp add: Arefl_def, auto)

\<comment> \<open>define disjoint strong (d,lH,PP)-bisimulation up-to-R' for a relation R\<close>
definition disj_dlHPP_Bisimulation_Up_To_R' :: 
  "'d \<Rightarrow> nat set \<Rightarrow> 'com Bisimulation_type 
  \<Rightarrow> 'com Bisimulation_type \<Rightarrow> bool"
where
"disj_dlHPP_Bisimulation_Up_To_R' d PP R' R \<equiv>
  SdlHPPB d PP R' \<and> (sym R) \<and> (trans R)
  \<and> (\<forall>(V,V') \<in> R. length V = length V') \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. 
    ((NDC d (V!i)) \<or> 
     (IDC d (V!i) (htchLoc (pp (V!i)))))) \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. \<forall>m1 m1' m2 \<alpha> p.
    (\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle> \<and> m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1')
    \<longrightarrow> (\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        (stepResultsinR p p' (R \<union> R')) \<and> (\<alpha>,\<alpha>') \<in> (R \<union> R') \<and> 
        (dhequality_alternative d PP (pp (V!i)) m2 m2')))"

\<comment> \<open>lemma about the transitivity of the union of symmetric and transitive relations under certain circumstances\<close>
lemma trans_RuR': 
  assumes transR: "trans R"
  assumes symR: "sym R"
  assumes transR': "trans R'"
  assumes symR': "sym R'"
  assumes eqlenR: "\<forall>(V,V') \<in> R. length V = length V'"
  assumes eqlenR': "\<forall>(V,V') \<in> R'. length V = length V'"
  assumes Areflassump: "(Arefl R \<inter> Arefl R') \<subseteq> {[]}"
  shows "trans (R \<union> R')"
proof -
 { 
   fix V V' V''
   assume p1: "(V,V') \<in> (R \<union> R')"
   assume p2: "(V',V'') \<in> (R \<union> R')"

   from p1 p2 have "(V,V'') \<in> (R \<union> R')"
     proof (auto)
         assume inR1: "(V,V') \<in> R"
         assume inR2: "(V',V'') \<in> R"
         from inR1 inR2 transR show "(V,V'') \<in> R"
           unfolding trans_def
           by blast
       next
         assume inR'1: "(V,V') \<in> R'"
         assume inR'2: "(V',V'') \<in> R'"
         assume notinR': "(V,V'') \<notin> R'"
         from inR'1 inR'2 transR' have inR': "(V,V'') \<in> R'"
           unfolding trans_def
           by blast
         from notinR' inR' have "False"
           by auto
         thus "(V,V'') \<in> R" ..
       next
         assume inR1: "(V,V') \<in> R"
         assume inR'2: "(V',V'') \<in> R'"
         from inR1 symR transR have "(V,V) \<in> R \<and> (V',V') \<in> R"
           unfolding sym_def trans_def
           by blast
         hence AreflR: "{V,V'} \<subseteq> Arefl R" by (simp add: Arefl_def)
         from inR'2 symR' transR' have "(V',V') \<in> R' \<and> (V'',V'') \<in> R'"
           unfolding sym_def trans_def
           by blast
         hence AreflR': "{V',V''} \<subseteq> Arefl R'" by (simp add: Arefl_def)

         from AreflR AreflR' Areflassump have V'empt: "V' = []" 
           by (simp add: Arefl_def, blast)
         with inR'2 eqlenR' have "V' = V''" by auto
         with inR1 show "(V, V'') \<in> R" by auto
       next
         assume inR'1: "(V,V') \<in> R'"
         assume inR2: "(V',V'') \<in> R"
         from inR'1 symR' transR' have "(V,V) \<in> R' \<and> (V',V') \<in> R'"
           unfolding sym_def trans_def
           by blast
         hence AreflR': "{V,V'} \<subseteq> Arefl R'" by (simp add: Arefl_def)
         from inR2 symR transR have "(V',V') \<in> R \<and> (V'',V'') \<in> R"
           unfolding sym_def trans_def
           by blast
         hence AreflR: "{V',V''} \<subseteq> Arefl R" by (simp add: Arefl_def)

         from AreflR AreflR' Areflassump have V'empt: "V' = []" 
           by (simp add: Arefl_def, blast)
         with inR'1 eqlenR' have "V' = V" by auto
         with inR2 show "(V, V'') \<in> R" by auto
       qed        
 }
 thus ?thesis unfolding trans_def by force

qed

lemma Up_To_Technique:
"\<lbrakk> disj_dlHPP_Bisimulation_Up_To_R' d PP R' R; 
  Arefl R \<inter> Arefl R' \<subseteq> {[]} \<rbrakk>
  \<Longrightarrow> SdlHPPB d PP (R \<union> R')"
proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def 
    Strong_dlHPP_Bisimulation_def, auto)
  assume symR': "sym R'"
  assume symR: "sym R"
  with symR' show "sym (R \<union> R')"
    by (simp add: sym_def)
next
  assume symR': "sym R'"
  assume symR: "sym R"
  assume transR': "trans R'"
  assume transR: "trans R"
  assume eqlenR': "\<forall>(V, V')\<in>R'. length V = length V'"
  assume eqlenR: "\<forall>(V, V')\<in>R. length V = length V'"
  assume areflassump: "Arefl R \<inter> Arefl R' \<subseteq> {[]}"
  from symR' symR transR' transR eqlenR' eqlenR areflassump trans_RuR'
  show "trans (R \<union> R')" 
    by blast
  \<comment> \<open>condition about IDC and NDC and equal length already proven above by auto tactic!\<close>
next
  fix V V' i m1 m1' m2 \<alpha> p
  assume inR': "(V,V') \<in> R'"
  assume irange: "i < length V"
  assume step: "\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
  assume dhequal: "m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1'"
  assume disjBisimUpTo: "\<forall>(V,V')\<in>R'. \<forall>i < length V. \<forall>m1 m1' m2 \<alpha> p.
    \<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle> \<and> m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1' \<longrightarrow>
    (\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
    stepResultsinR p p' R' \<and> (\<alpha>, \<alpha>') \<in> R' \<and>
    dhequality_alternative d PP (pp (V!i)) m2 m2')"
  from inR' irange step dhequal disjBisimUpTo show "\<exists>p' \<alpha>' m2'.
    \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> stepResultsinR p p' (R \<union> R') \<and>
    ((\<alpha>,\<alpha>') \<in> R \<or> (\<alpha>,\<alpha>') \<in> R') \<and> 
    dhequality_alternative d PP (pp (V!i)) m2 m2'"
    by (simp add: stepResultsinR_def,fastforce)
qed

  
lemma Union_Strong_dlHPP_Bisim:
"\<lbrakk> SdlHPPB d PP R; SdlHPPB d PP R'; 
  Arefl R \<inter> Arefl R' \<subseteq> {[]} \<rbrakk>
  \<Longrightarrow> SdlHPPB d PP (R \<union> R')"
by (rule Up_To_Technique, simp_all add: 
  disj_dlHPP_Bisimulation_Up_To_R'_def 
  Strong_dlHPP_Bisimulation_def stepResultsinR_def, fastforce)


lemma adding_emptypair_keeps_SdlHPPB:
  assumes SdlHPP: "SdlHPPB d PP R"
  shows "SdlHPPB d PP (R \<union> {([],[])})"
proof -
  have SdlHPPemp: "SdlHPPB d PP {([],[])}"
    by (simp add: Strong_dlHPP_Bisimulation_def sym_def trans_def)

  have commonDom: "Domain R \<inter> Domain {([],[])} \<subseteq> {[]}"
    by auto

  with commonArefl_subset_commonDomain have Areflassump:
    "Arefl R \<inter> Arefl {([],[])} \<subseteq> {[]}"
    by force

  with SdlHPP SdlHPPemp Union_Strong_dlHPP_Bisim show 
    "SdlHPPB d PP (R \<union> {([],[])})"
    by force
qed

end

end
