(*<*)
(*
   Title:  Theory  DataDependenciesCaseStudy.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
(*>*)

section "Case Study: Verification of Properties"
 
theory DataDependenciesCaseStudy
  imports DataDependencies
begin


subsection \<open>Correct composition of components\<close>

\<comment> \<open>the lemmas  AbstrLevels X Y with corresponding proofs can be composend\<close>
\<comment> \<open>and proven automatically, their proofs are identical\<close>
lemma AbstrLevels_A1_A11:
  assumes "sA1 \<in> AbstrLevel i"
  shows "sA11 \<notin> AbstrLevel i"
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)

lemma AbstrLevels_A1_A12:
  assumes "sA1 \<in> AbstrLevel i"
  shows "sA12 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A2_A21:
  assumes "sA2 \<in> AbstrLevel i"
  shows "sA21 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A2_A22:
  assumes "sA2 \<in> AbstrLevel i"
  shows "sA22 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A2_A23:
  assumes "sA2 \<in> AbstrLevel i"
  shows "sA23 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A3_A31:
  assumes "sA3 \<in> AbstrLevel i"
  shows "sA31 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A3_A32:
  assumes "sA3 \<in> AbstrLevel i"
  shows "sA32 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A4_A41:
  assumes "sA4 \<in> AbstrLevel i"
  shows "sA41 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A4_A42:
  assumes "sA4 \<in> AbstrLevel i"
  shows "sA42 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A7_A71:
  assumes "sA7 \<in> AbstrLevel i"
  shows "sA71 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A7_A72:
  assumes "sA7 \<in> AbstrLevel i"
  shows "sA72 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)

lemma AbstrLevels_A8_A81:
  assumes "sA8 \<in> AbstrLevel i"
  shows "sA81 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)

lemma AbstrLevels_A8_A82:
  assumes "sA8 \<in> AbstrLevel i"
  shows "sA82 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A9_A91:
  assumes "sA9 \<in> AbstrLevel i"
  shows "sA91 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A9_A92:
  assumes "sA9 \<in> AbstrLevel i"
  shows "sA92 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_A9_A93:
  assumes "sA9 \<in> AbstrLevel i"
  shows "sA93 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S1_A12:
  assumes "sS1 \<in> AbstrLevel i"
  shows "sA12 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S2_A11:
  assumes "sS2 \<in> AbstrLevel i"
  shows "sA11 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S3_A21:
  assumes "sS3 \<in> AbstrLevel i"
  shows "sA21 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4_A23:
  assumes "sS4 \<in> AbstrLevel i"
  shows "sA23 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S5_A32:
  assumes "sS5 \<in> AbstrLevel i"
  shows "sA32 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S6_A22:
  assumes "sS6 \<in> AbstrLevel i"
  shows "sA22 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S6_A31:
  assumes "sS6 \<in> AbstrLevel i"
  shows "sA31 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S6_A41:
  assumes "sS6 \<in> AbstrLevel i"
  shows "sA41 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S7_A42:
  assumes "sS7 \<in> AbstrLevel i"
  shows "sA42 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S8_A5:
  assumes "sS8 \<in> AbstrLevel i"
  shows "sA5 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S9_A6:
  assumes "sS9 \<in> AbstrLevel i"
  shows "sA6 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S10_A71:
  assumes "sS10 \<in> AbstrLevel i"
  shows "sA71 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S11_A72:
  assumes "sS11 \<in> AbstrLevel i"
  shows "sA72 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S12_A81:
  assumes "sS12 \<in> AbstrLevel i"
  shows "sA81 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S12_A91:
  assumes "sS12 \<in> AbstrLevel i"
  shows "sA91 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S13_A92:
  assumes "sS13 \<in> AbstrLevel i"
  shows "sA92 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S14_A82:
  assumes "sS14 \<in> AbstrLevel i"
  shows "sA82 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S15_A93:
  assumes "sS15 \<in> AbstrLevel i"
  shows "sA93 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S1opt_A11:
  assumes "sS1opt \<in> AbstrLevel i"
  shows "sA11 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S1opt_A12:
  assumes "sS1opt \<in> AbstrLevel i"
  shows "sA12 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4opt_A23:
  assumes "sS4opt \<in> AbstrLevel i"
  shows "sA23 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4opt_A32:
  assumes "sS4opt \<in> AbstrLevel i"
  shows "sA32 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4opt_A22:
  assumes "sS4opt \<in> AbstrLevel i"
  shows "sA22 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4opt_A31:
  assumes "sS4opt \<in> AbstrLevel i"
  shows "sA31 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S4opt_A41:
  assumes "sS4opt \<in> AbstrLevel i"
  shows "sA41 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S7opt_A42:
  assumes "sS7opt \<in> AbstrLevel i"
  shows "sA42 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S7opt_A5:
  assumes "sS7opt \<in> AbstrLevel i"
  shows "sA5 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S11opt_A72:
  assumes "sS11opt \<in> AbstrLevel i"
  shows "sA72 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S11opt_A82:
  assumes "sS11opt \<in> AbstrLevel i"
  shows "sA82 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma AbstrLevels_S11opt_A93:
  assumes "sS11opt \<in> AbstrLevel i"
  shows "sA93 \<notin> AbstrLevel i"
(*<*)
using assms 
by (induct i, simp add: AbstrLevel0, simp add:  AbstrLevel1, simp add:  AbstrLevel2,  simp add:  AbstrLevel3)
(*>*)


lemma correctCompositionDiffLevelsA1: "correctCompositionDiffLevels sA1"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A1_A11 AbstrLevels_A1_A12)(*>*)


lemma correctCompositionDiffLevelsA2: "correctCompositionDiffLevels sA2"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A2_A21 AbstrLevels_A2_A22 AbstrLevels_A2_A23)(*>*)


lemma correctCompositionDiffLevelsA3: "correctCompositionDiffLevels sA3"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A3_A31 AbstrLevels_A3_A32)(*>*)


lemma correctCompositionDiffLevelsA4: "correctCompositionDiffLevels sA4"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A4_A41 AbstrLevels_A4_A42)(*>*)


\<comment> \<open>lemmas  correctCompositionDiffLevelsX and corresponding proofs\<close>
\<comment> \<open>are identical for all elementary components, they can be constructed automatically\<close> 
lemma correctCompositionDiffLevelsA5: "correctCompositionDiffLevels sA5"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA6: "correctCompositionDiffLevels sA6"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA7: "correctCompositionDiffLevels sA7"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A7_A71 AbstrLevels_A7_A72)(*>*)

lemma correctCompositionDiffLevelsA8: "correctCompositionDiffLevels sA8"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A8_A81 AbstrLevels_A8_A82)(*>*)

lemma correctCompositionDiffLevelsA9: "correctCompositionDiffLevels sA9"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_A9_A91 AbstrLevels_A9_A92 AbstrLevels_A9_A93)(*>*)

lemma correctCompositionDiffLevelsA11: "correctCompositionDiffLevels sA11"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA12: "correctCompositionDiffLevels sA12"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA21: "correctCompositionDiffLevels sA21"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA22: "correctCompositionDiffLevels sA22"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA23: "correctCompositionDiffLevels sA23"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA31: "correctCompositionDiffLevels sA31"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA32: "correctCompositionDiffLevels sA32"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA41: "correctCompositionDiffLevels sA41"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA42: "correctCompositionDiffLevels sA42"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA71: "correctCompositionDiffLevels sA71"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA72: "correctCompositionDiffLevels sA72"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA81: "correctCompositionDiffLevels sA81"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA82: "correctCompositionDiffLevels sA82"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA91: "correctCompositionDiffLevels sA91"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA92: "correctCompositionDiffLevels sA92"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsA93: "correctCompositionDiffLevels sA93"
(*<*)by (simp add: correctCompositionDiffLevels_def) (*>*)

lemma correctCompositionDiffLevelsS1: "correctCompositionDiffLevels sS1"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S1_A12) (*>*)

lemma correctCompositionDiffLevelsS2: "correctCompositionDiffLevels sS2"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S2_A11) (*>*)

lemma correctCompositionDiffLevelsS3: "correctCompositionDiffLevels sS3"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S3_A21) (*>*)

lemma correctCompositionDiffLevelsS4: "correctCompositionDiffLevels sS4"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S4_A23) (*>*)

lemma correctCompositionDiffLevelsS5: "correctCompositionDiffLevels sS5"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S5_A32) (*>*)

lemma correctCompositionDiffLevelsS6: "correctCompositionDiffLevels sS6"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S6_A22 AbstrLevels_S6_A31 AbstrLevels_S6_A41) (*>*)

lemma correctCompositionDiffLevelsS7: "correctCompositionDiffLevels sS7"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S7_A42) (*>*)

lemma correctCompositionDiffLevelsS8: "correctCompositionDiffLevels sS8"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S8_A5) (*>*)

lemma correctCompositionDiffLevelsS9: "correctCompositionDiffLevels sS9"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S9_A6) (*>*)

lemma correctCompositionDiffLevelsS10: "correctCompositionDiffLevels sS10"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S10_A71) (*>*)

lemma correctCompositionDiffLevelsS11: "correctCompositionDiffLevels sS11"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S11_A72) (*>*)

lemma correctCompositionDiffLevelsS12: "correctCompositionDiffLevels sS12"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S12_A81 AbstrLevels_S12_A91) (*>*)

lemma correctCompositionDiffLevelsS13: "correctCompositionDiffLevels sS13"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S13_A92) (*>*)

lemma correctCompositionDiffLevelsS14: "correctCompositionDiffLevels sS14"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S14_A82) (*>*)

lemma correctCompositionDiffLevelsS15: "correctCompositionDiffLevels sS15"
(*<*)by (simp add: correctCompositionDiffLevels_def AbstrLevels_S15_A93) (*>*)

lemma correctCompositionDiffLevelsS1opt: "correctCompositionDiffLevels sS1opt"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S1opt_A11 AbstrLevels_S1opt_A12) (*>*)

lemma correctCompositionDiffLevelsS4opt: "correctCompositionDiffLevels sS4opt"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S4opt_A22 
      AbstrLevels_S4opt_A23  AbstrLevels_S4opt_A31  
      AbstrLevels_S4opt_A32  AbstrLevels_S4opt_A41) (*>*)

lemma correctCompositionDiffLevelsS7opt: "correctCompositionDiffLevels sS7opt"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S7opt_A42 AbstrLevels_S7opt_A5) (*>*)

lemma correctCompositionDiffLevelsS11opt: "correctCompositionDiffLevels sS11opt"
(*<*)by (simp add: correctCompositionDiffLevels_def  AbstrLevels_S11opt_A72 
        AbstrLevels_S11opt_A82 AbstrLevels_S11opt_A93) (*>*)

lemma correctCompositionDiffLevelsSYSTEM_holds:
"correctCompositionDiffLevelsSYSTEM"
(*<*)by (simp add: correctCompositionDiffLevelsSYSTEM_def, clarify, case_tac S, 
simp add: correctCompositionDiffLevelsA1, 
simp add: correctCompositionDiffLevelsA2,
simp add: correctCompositionDiffLevelsA3,
simp add: correctCompositionDiffLevelsA4,
simp add: correctCompositionDiffLevelsA5,
simp add: correctCompositionDiffLevelsA6,
simp add: correctCompositionDiffLevelsA7,
simp add: correctCompositionDiffLevelsA8,
simp add: correctCompositionDiffLevelsA9,
simp add: correctCompositionDiffLevelsA11,
simp add: correctCompositionDiffLevelsA12,
simp add: correctCompositionDiffLevelsA21,
simp add: correctCompositionDiffLevelsA22,
simp add: correctCompositionDiffLevelsA23,
simp add: correctCompositionDiffLevelsA31,
simp add: correctCompositionDiffLevelsA32,
simp add: correctCompositionDiffLevelsA41,
simp add: correctCompositionDiffLevelsA42,
simp add: correctCompositionDiffLevelsA71,
simp add: correctCompositionDiffLevelsA72,
simp add: correctCompositionDiffLevelsA81,
simp add: correctCompositionDiffLevelsA82,
simp add: correctCompositionDiffLevelsA91,
simp add: correctCompositionDiffLevelsA92,
simp add: correctCompositionDiffLevelsA93,
simp add: correctCompositionDiffLevelsS1,
simp add: correctCompositionDiffLevelsS2,
simp add: correctCompositionDiffLevelsS3,
simp add: correctCompositionDiffLevelsS4,
simp add: correctCompositionDiffLevelsS5,
simp add: correctCompositionDiffLevelsS6,
simp add: correctCompositionDiffLevelsS7,
simp add: correctCompositionDiffLevelsS8,
simp add: correctCompositionDiffLevelsS9,
simp add: correctCompositionDiffLevelsS10,
simp add: correctCompositionDiffLevelsS11,
simp add: correctCompositionDiffLevelsS12,
simp add: correctCompositionDiffLevelsS13,
simp add: correctCompositionDiffLevelsS14,
simp add: correctCompositionDiffLevelsS15,
simp add: correctCompositionDiffLevelsS1opt,
simp add: correctCompositionDiffLevelsS4opt,
simp add: correctCompositionDiffLevelsS7opt, 
simp add: correctCompositionDiffLevelsS11opt)(*>*)

lemma correctCompositionVARSYSTEM_holds:
"correctCompositionVARSYSTEM"
by (simp add: correctCompositionVARSYSTEM_def, clarify, case_tac S, (simp add: correctCompositionVAR_def)+)

lemma correctDeCompositionVARSYSTEM_holds:
"correctDeCompositionVARSYSTEM"
by (simp add: correctDeCompositionVARSYSTEM_def, clarify, case_tac S, (simp add: correctDeCompositionVAR_def)+)


subsection \<open>Correct specification of the relations between channels\<close>

lemma OUTfromChCorrect_data1: "OUTfromChCorrect data1"
by (simp add: OUTfromChCorrect_def)

lemma OUTfromChCorrect_data2: "OUTfromChCorrect data2"
by (metis IN.simps(27) OUT.simps(27) OUTfromCh.simps(2) OUTfromChCorrect_def insertI1)

lemma OUTfromChCorrect_data3: "OUTfromChCorrect data3"
by (metis OUTfromCh.simps(3) OUTfromChCorrect_def)

lemma OUTfromChCorrect_data4: "OUTfromChCorrect data4"
by (metis IN.simps(2) OUT.simps(2) OUTfromCh.simps(4) OUTfromChCorrect_def insertI1 singleton_iff)

lemma OUTfromChCorrect_data5: "OUTfromChCorrect data5"
by  (simp add: OUTfromChCorrect_def, metis IN.simps(14) OUT.simps(14) insertI1)

lemma OUTfromChCorrect_data6: "OUTfromChCorrect data6"
by  (simp add: OUTfromChCorrect_def, metis IN.simps(15) OUT.simps(15) insertI1)

lemma OUTfromChCorrect_data7: "OUTfromChCorrect data7"
by (simp add: OUTfromChCorrect_def, metis IN.simps(16) OUT.simps(16) insertI1)

lemma OUTfromChCorrect_data8: "OUTfromChCorrect data8"
by (simp add: OUTfromChCorrect_def, metis IN.simps(18) OUT.simps(18) insertI1) 

 
lemma OUTfromChCorrect_data9: "OUTfromChCorrect data9"
by (simp add: OUTfromChCorrect_def , metis IN.simps(33) OUT.simps(33) singleton_iff)

lemma OUTfromChCorrect_data10: "OUTfromChCorrect data10"
by (simp add: OUTfromChCorrect_def)

lemma OUTfromChCorrect_data11: "OUTfromChCorrect data11"
by (simp add: OUTfromChCorrect_def, metis (full_types) IN.simps(2) 
OUT.simps(2) OUT.simps(31) Un_empty_right Un_insert_left Un_insert_right insertI1)

lemma OUTfromChCorrect_data12: "OUTfromChCorrect data12"
by (simp add: OUTfromChCorrect_def)

lemma OUTfromChCorrect_data13: "OUTfromChCorrect data13"
by (simp add: OUTfromChCorrect_def)

lemma OUTfromChCorrect_data14: "OUTfromChCorrect data14"
by (metis OUTfromCh.simps(14) OUTfromChCorrect_def)

lemma OUTfromChCorrect_data15: "OUTfromChCorrect data15"
by (metis OUTfromCh.simps(15) OUTfromChCorrect_def)

lemma OUTfromChCorrect_data16: "OUTfromChCorrect data16"
by (metis OUTfromCh.simps(16) OUTfromChCorrect_def)

lemma OUTfromChCorrect_data17: "OUTfromChCorrect data17"
proof - 
  have "data17 \<in> OUT sA71 \<and> data15 \<in> IN sA71"
    by (metis IN.simps(19) OUT.simps(19) insertI1)  
  thus ?thesis by (metis IN.simps(19) OUTfromCh.simps(17) OUTfromChCorrect_def) 
qed

lemma OUTfromChCorrect_data18: "OUTfromChCorrect data18"
by (simp add: OUTfromChCorrect_def, metis IN.simps(20) OUT.simps(20) insertI1)

lemma OUTfromChCorrect_data19: "OUTfromChCorrect data19"
by (metis OUTfromCh.simps(19) OUTfromChCorrect_def)

lemma OUTfromChCorrect_data20: "OUTfromChCorrect data20"
by  (simp add: OUTfromChCorrect_def, metis IN.simps(21) OUT.simps(21) insertI1 insert_subset subset_insertI)

lemma OUTfromChCorrect_data21: "OUTfromChCorrect data21"
by (simp add: OUTfromChCorrect_def, metis (full_types) 
IN.simps(22) OUT.simps(22) insertI1 insert_subset subset_insertI)

lemma OUTfromChCorrect_data22: "OUTfromChCorrect data22"
by (simp add: OUTfromChCorrect_def, metis (full_types) IN.simps(23) OUT.simps(23) insertI1)

lemma OUTfromChCorrect_data23: "OUTfromChCorrect data23"
by (simp add: OUTfromChCorrect_def, metis (full_types) IN.simps(9) OUT.simps(9) insert_subset subset_insertI)

lemma OUTfromChCorrect_data24: "OUTfromChCorrect data24"
by (simp add: OUTfromChCorrect_def, metis IN.simps(9) OUT.simps(9) insertI1 insert_subset subset_insertI)

lemma OUTfromChCorrectSYSTEM_holds: "OUTfromChCorrectSYSTEM"
by (simp add: OUTfromChCorrectSYSTEM_def,  clarify, case_tac x,
simp add: OUTfromChCorrect_data1, simp add: OUTfromChCorrect_data2, 
simp add: OUTfromChCorrect_data3, simp add: OUTfromChCorrect_data4,  
simp add: OUTfromChCorrect_data5, simp add: OUTfromChCorrect_data6, 
simp add: OUTfromChCorrect_data7, simp add: OUTfromChCorrect_data8,
simp add: OUTfromChCorrect_data9, simp add: OUTfromChCorrect_data10,
simp add: OUTfromChCorrect_data11, simp add: OUTfromChCorrect_data12,
simp add: OUTfromChCorrect_data13, simp add: OUTfromChCorrect_data14, 
simp add: OUTfromChCorrect_data15, simp add: OUTfromChCorrect_data16,
simp add: OUTfromChCorrect_data17, simp add: OUTfromChCorrect_data18,
simp add: OUTfromChCorrect_data19, simp add: OUTfromChCorrect_data20,
simp add: OUTfromChCorrect_data21, simp add: OUTfromChCorrect_data22, 
simp add: OUTfromChCorrect_data23, simp add: OUTfromChCorrect_data24)

lemma OUTfromVCorrect1_data1: "OUTfromVCorrect1 data1"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data2: "OUTfromVCorrect1 data2"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data3: "OUTfromVCorrect1 data3"
proof - 
  have "data3 \<in> OUT sA41 \<and> stA4 \<in> VAR sA41"
    by (metis OUT.simps(17) VAR.simps(17) insertI1) 
  thus ?thesis by (metis OUTfromV.simps(3) OUTfromVCorrect1_def VAR.simps(17)) 
qed

lemma OUTfromVCorrect1_data4: "OUTfromVCorrect1 data4"
by (simp add: OUTfromVCorrect1_def, metis (full_types) OUT.simps(2) VAR.simps(2) insertI1) 

lemma OUTfromVCorrect1_data5: "OUTfromVCorrect1 data5"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data6: "OUTfromVCorrect1 data6"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data7: "OUTfromVCorrect1 data7"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data8: "OUTfromVCorrect1 data8"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data9: "OUTfromVCorrect1 data9"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data10: "OUTfromVCorrect1 data10"
proof -
  have "data10 \<in> OUT sA12 \<and> stA1 \<in> VAR sA12"
    by (metis OUT.simps(11) VAR.simps(11) insertI1) 
  thus ?thesis by (metis OUT.simps(26) OUTfromV.simps(10) OUTfromVCorrect1_def VAR.simps(26) insertI1) 
qed 

lemma OUTfromVCorrect1_data11: "OUTfromVCorrect1 data11"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data12: "OUTfromVCorrect1 data12"
proof - 
  have "data12 \<in> OUT sA22 \<and> stA2 \<in> VAR sA22"
    by (metis (full_types) OUT.simps(13) VAR.simps(13) insertCI) 
  thus ?thesis by (metis OUTfromV.simps(12) OUTfromVCorrect1_def VAR.simps(13)) 
qed

lemma OUTfromVCorrect1_data13: "OUTfromVCorrect1 data13"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data14: "OUTfromVCorrect1 data14"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data15: "OUTfromVCorrect1 data15"
proof -
  have A6ch:"data15 \<in> OUT sA6 \<and> stA6 \<in> VAR sA6"
    by (metis OUT.simps(6) VAR.simps(6) insertI1) 
  thus ?thesis by (simp add: OUTfromVCorrect1_def, metis A6ch) 
qed

lemma OUTfromVCorrect1_data16: "OUTfromVCorrect1 data16"
proof -
  have A6ch:"data16 \<in> OUT sA6 \<and> stA6 \<in> VAR sA6"
    by (metis (full_types) OUT.simps(6) VAR.simps(6) insertCI)
  thus ?thesis by (simp add: OUTfromVCorrect1_def, metis A6ch) 
qed

lemma OUTfromVCorrect1_data17: "OUTfromVCorrect1 data17"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data18: "OUTfromVCorrect1 data18"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data19: "OUTfromVCorrect1 data19"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data20: "OUTfromVCorrect1 data20"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data21: "OUTfromVCorrect1 data21"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data22: "OUTfromVCorrect1 data22"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data23: "OUTfromVCorrect1 data23"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1_data24: "OUTfromVCorrect1 data24"
by (simp add: OUTfromVCorrect1_def)

lemma OUTfromVCorrect1SYSTEM_holds: "OUTfromVCorrect1SYSTEM"
by (simp add: OUTfromVCorrect1SYSTEM_def, clarify, case_tac x, 
simp add: OUTfromVCorrect1_data1, simp add: OUTfromVCorrect1_data2,
simp add: OUTfromVCorrect1_data3, simp add: OUTfromVCorrect1_data4, 
simp add: OUTfromVCorrect1_data5, simp add: OUTfromVCorrect1_data6, 
simp add: OUTfromVCorrect1_data7, simp add: OUTfromVCorrect1_data8, 
simp add: OUTfromVCorrect1_data9, simp add: OUTfromVCorrect1_data10, 
simp add: OUTfromVCorrect1_data11, simp add: OUTfromVCorrect1_data12, 
simp add: OUTfromVCorrect1_data13, simp add: OUTfromVCorrect1_data14, 
simp add: OUTfromVCorrect1_data15, simp add: OUTfromVCorrect1_data16, 
simp add: OUTfromVCorrect1_data17, simp add: OUTfromVCorrect1_data18,
simp add: OUTfromVCorrect1_data19, simp add: OUTfromVCorrect1_data20,
simp add: OUTfromVCorrect1_data21, simp add: OUTfromVCorrect1_data22,
simp add: OUTfromVCorrect1_data23, simp add: OUTfromVCorrect1_data24)

lemma OUTfromVCorrect2SYSTEM: "OUTfromVCorrect2SYSTEM"
by (simp add: OUTfromVCorrect2SYSTEM_def, auto, case_tac x,
      ((simp add: OUTfromVCorrect2_def, auto, case_tac v, auto) | 
       (simp add: OUTfromVCorrect2_def) )+)

lemma OUTfromV_VARto_holds:
"OUTfromV_VARto"
by (simp add: OUTfromV_VARto_def, auto, (case_tac x, auto), (case_tac v, auto))

lemma VARfromCorrectSYSTEM_holds:
"VARfromCorrectSYSTEM"
by (simp add: VARfromCorrectSYSTEM_def AbstrLevel0 AbstrLevel1)

lemma VARtoCorrectSYSTEM_holds:
"VARtoCorrectSYSTEM"
by (simp add: VARtoCorrectSYSTEM_def AbstrLevel0 AbstrLevel1)

lemma VARusefulSYSTEM_holds:
"VARusefulSYSTEM"
by (simp add: VARusefulSYSTEM_def, auto, case_tac v, auto)


subsection \<open>Elementary components\<close>

\<comment> \<open>On the abstraction level 0 only the components sA5 and sA6 are elementary\<close>

lemma NOT_elementaryCompDD_sA1:  "\<not> elementaryCompDD sA1" 
proof -
  have "outSetCorelated data2 \<inter> outSetCorelated data10 = {}"
  by (metis OUTfromV.simps(2) inf_bot_left outSetCorelatedEmpty1) 
  thus ?thesis by (simp add: elementaryCompDD_def)
qed

lemma NOT_elementaryCompDD_sA2: "\<not> elementaryCompDD sA2" 
proof -
  have "outSetCorelated data5 \<inter> outSetCorelated data11 = {}"
  by (metis OUTfromV.simps(5) inf_bot_right inf_commute outSetCorelatedEmpty1)
  thus ?thesis by (simp add: elementaryCompDD_def)
qed 

lemma NOT_elementaryCompDD_sA3:  "\<not> elementaryCompDD sA3" 
proof -
  have "outSetCorelated data6 \<inter> outSetCorelated data7 = {}"
  by (metis OUTfromV.simps(7) inf_bot_right outSetCorelatedEmpty1) 
  thus ?thesis by (simp add: elementaryCompDD_def)
qed

lemma NOT_elementaryCompDD_sA4:  "\<not> elementaryCompDD sA4" 
proof -
  have "outSetCorelated data3 \<inter> outSetCorelated data8 = {}"
  by (metis OUTfromV.simps(8) inf_bot_left inf_commute outSetCorelatedEmpty1)
  thus ?thesis by (simp add: elementaryCompDD_def)  
qed

lemma elementaryCompDD_sA5:  "elementaryCompDD sA5" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA6:  "elementaryCompDD sA6" 
proof -
  have oSet15:"outSetCorelated data15 \<noteq> {}" 
    by (simp add: outSetCorelated_def, auto)
  have oSet16:"outSetCorelated data16 \<noteq> {}"
    by (simp add: outSetCorelated_def, auto)
  have "outSetCorelated data15 \<inter> outSetCorelated data16 \<noteq> {}"
    by (simp add: outSetCorelated_def, auto)
  with oSet15 oSet16 show ?thesis by (simp add: elementaryCompDD_def, auto) 
qed

lemma NOT_elementaryCompDD_sA7:  "\<not> elementaryCompDD sA7" 
proof - 
  have "outSetCorelated data17 \<inter> outSetCorelated data18 = {}"
  by (metis (full_types) OUTfromV.simps(17) disjoint_iff_not_equal empty_iff outSetCorelatedEmpty1) 
  thus ?thesis by  (simp add: elementaryCompDD_def)
qed

lemma NOT_elementaryCompDD_sA8:  "\<not> elementaryCompDD sA8" 
proof - 
  have "outSetCorelated data20 \<inter> outSetCorelated data21 = {}"
  by (metis OUTfromV.simps(21) inf_bot_right outSetCorelatedEmpty1)
  thus ?thesis by  (simp add: elementaryCompDD_def)
qed

lemma NOT_elementaryCompDD_sA9:  "\<not> elementaryCompDD sA9" 
proof - 
  have "outSetCorelated data23 \<inter> outSetCorelated data24 = {}"
  by (metis (full_types) OUTfromV.simps(23) disjoint_iff_not_equal empty_iff outSetCorelatedEmpty1)
  thus ?thesis by  (simp add: elementaryCompDD_def)  
qed

\<comment> \<open>On the abstraction level 1 all components are elementary\<close>

lemma elementaryCompDD_sA11:  "elementaryCompDD sA11" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA12:  "elementaryCompDD sA12" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA21: "elementaryCompDD sA21" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA22: "elementaryCompDD sA22" 
proof - 
  have oSet4:"outSetCorelated data4 \<noteq> {}"  
    by (simp add: outSetCorelated_def, auto)
  have oSet12:"outSetCorelated data12 \<noteq> {}"  
    by (simp add: outSetCorelated_def, auto)
  have "outSetCorelated data4 \<inter> outSetCorelated data12 \<noteq> {}"
    by (simp add: outSetCorelated_def, auto)
  with oSet4 oSet12 show ?thesis 
    by  (simp add: elementaryCompDD_def, auto)
qed 

lemma elementaryCompDD_sA23: "elementaryCompDD sA23" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA31: "elementaryCompDD sA31" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA32: "elementaryCompDD sA32" 
by  (simp add: elementaryCompDD_def)


lemma elementaryCompDD_sA41: "elementaryCompDD sA41" 
by  (simp add: elementaryCompDD_def) 

lemma elementaryCompDD_sA42: "elementaryCompDD sA42" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA71: "elementaryCompDD sA71" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA72: "elementaryCompDD sA72" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA81: "elementaryCompDD sA81" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA82: "elementaryCompDD sA82" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA91: "elementaryCompDD sA91" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA92: "elementaryCompDD sA92" 
by  (simp add: elementaryCompDD_def)

lemma elementaryCompDD_sA93: "elementaryCompDD sA93" 
by  (simp add: elementaryCompDD_def)

subsection \<open>Source components\<close>

\<comment> \<open>Abstraction level 0\<close>

lemma A5_NotDSource_level0: "isNotDSource level0 sA5"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)

lemma DSourcesA1_L0: "DSources level0 sA1 = {}"
by (simp add: DSources_def, auto, case_tac "x", auto) 

lemma DSourcesA2_L0: "DSources level0 sA2 = { sA1, sA4}"
by (simp add: DSources_def AbstrLevel0, auto) 

lemma DSourcesA3_L0: "DSources level0 sA3 = { sA2 }"
by (simp add: DSources_def AbstrLevel0, auto) 

lemma DSourcesA4_L0: "DSources level0 sA4 = { sA3 }"
by (simp add: DSources_def AbstrLevel0, auto) 

lemma DSourcesA5_L0: "DSources level0 sA5 = { sA4 }"
by (simp add: DSources_def AbstrLevel0, auto)  

lemma DSourcesA6_L0: "DSources level0 sA6 = {}"
by (simp add: DSources_def, auto, case_tac "x", auto) 

lemma DSourcesA7_L0: "DSources level0 sA7 = {sA6}"
by (simp add: DSources_def AbstrLevel0, auto) 

lemma DSourcesA8_L0: "DSources level0 sA8 = {sA7, sA9}"
by (simp add: DSources_def AbstrLevel0, force)

lemma DSourcesA9_L0: "DSources level0 sA9 = {sA8}"
by (simp add: DSources_def AbstrLevel0, auto) 

lemma A1_DAcc_level0: "DAcc level0 sA1 = { sA2 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A2_DAcc_level0: "DAcc level0 sA2 = { sA3 }" 
by (simp add: DAcc_def  AbstrLevel0, force)

lemma A3_DAcc_level0: "DAcc level0 sA3 = { sA4 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A4_DAcc_level0: "DAcc level0 sA4 = { sA2, sA5 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A5_DAcc_level0: "DAcc level0 sA5 = {}" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A6_DAcc_level0: "DAcc level0 sA6 = { sA7 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A7_DAcc_level0: "DAcc level0 sA7 = { sA8 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A8_DAcc_level0: "DAcc level0 sA8 = { sA9 }" 
by (simp add: DAcc_def  AbstrLevel0, auto)

lemma A9_DAcc_level0: "DAcc level0 sA9 = { sA8 }" 
by (simp add: DAcc_def  AbstrLevel0, force)

lemma A8_NSources:
"\<forall> C \<in> (AbstrLevel level0). (C \<noteq> sA9 \<and> C \<noteq> sA8 \<longrightarrow> sA8 \<notin> (Sources level0 C))"
by (metis A8_DAcc_level0 A9_DAcc_level0 singleDSourceLoop)

lemma A9_NSources:
"\<forall> C \<in> (AbstrLevel level0). (C \<noteq> sA9 \<and> C \<noteq> sA8 \<longrightarrow> sA9 \<notin> (Sources level0 C))"
by (metis A8_DAcc_level0 A9_DAcc_level0 singleDSourceLoop)

lemma A7_Acc:
"(Acc level0 sA7) = {sA8, sA9}"
  by (metis A7_DAcc_level0 A8_DAcc_level0 A9_DAcc_level0 AccDef AccSigleLoop insert_commute) 

lemma A7_NSources:
"\<forall> C \<in> (AbstrLevel level0). (C \<noteq> sA9 \<and> C \<noteq> sA8 \<longrightarrow> sA7 \<notin> (Sources level0 C))"
by (metis A7_Acc Acc_Sources insert_iff singleton_iff)

lemma A5_Acc: "(Acc level0 sA5) = {}"
by (metis A5_NotDSource_level0 isNotDSource_EmptyAcc)

lemma A6_Acc:
"(Acc level0 sA6) = {sA7, sA8, sA9}"
proof -
  have daA6:  "DAcc level0 sA6 = { sA7 }"  by (rule A6_DAcc_level0)
  hence "(\<Union> S \<in> (DAcc level0 sA6). (Acc level0 S)) = (Acc level0 sA7)"  by simp
  hence aA6:"(\<Union> S \<in> (DAcc level0 sA6). (Acc level0 S)) = { sA8, sA9 }" by (simp add: A7_Acc)
  have "(Acc level0 sA6) = (DAcc level0 sA6) \<union> (\<Union> S \<in> (DAcc level0 sA6). (Acc level0 S))"  
    by (rule AccDef)
  with daA6 aA6 show ?thesis by auto
qed

lemma A6_NSources:
"\<forall> C \<in> (AbstrLevel level0). (C \<noteq> sA9 \<and> C \<noteq> sA8 \<and> C \<noteq> sA7 \<longrightarrow> sA6 \<notin> (Sources level0 C))"
by (metis (full_types) A6_Acc A7_Acc Acc_SourcesNOT insert_iff singleton_iff)

lemma SourcesA1_L0: "Sources level0 sA1 = {}"  
by (simp add: DSourcesA1_L0 DSourcesEmptySources) 
     
lemma SourcesA2_L0: "Sources level0 sA2 = { sA1, sA2, sA3, sA4 }"
proof 
  show "Sources level0 sA2 \<subseteq> {sA1, sA2, sA3, sA4}"
  proof -
    have A2level0:"sA2 \<in> (AbstrLevel level0)" by (simp add: AbstrLevel0)
    have sgA5:"sA5 \<notin> Sources level0 sA2" 
      by (metis A5_NotDSource_level0 DSource_level NoDSourceNoSource 
            allNotDSource_NotSource isNotSource_Sources)
     from A2level0 have sgA6:"sA6 \<notin> Sources level0 sA2" by (simp add: A6_NSources)
     from A2level0 have sgA7:"sA7 \<notin> Sources level0 sA2" by (simp add: A7_NSources)
     from A2level0 have sgA8:"sA8 \<notin> Sources level0 sA2" by (simp add: A8_NSources)
     from A2level0 have sgA9:"sA9 \<notin> Sources level0 sA2" by (simp add: A9_NSources)
     have "Sources level0 sA2 \<subseteq> {sA1, sA2, sA3, sA4, sA5, sA6, sA7, sA8, sA9}"
        by (metis AbstrLevel0 SourcesLevelX) 
     with sgA5 sgA6 sgA7 sgA8 sgA9 show "Sources level0 sA2 \<subseteq> {sA1, sA2, sA3, sA4}"
        by blast   
  qed
next
  show "{sA1, sA2, sA3, sA4} \<subseteq> Sources level0 sA2"
  proof -
    have dsA4:"{ sA3 } \<subseteq> Sources level0 sA2"
       by (metis DSource_Sources DSourcesA2_L0 DSourcesA4_L0 
             Sources_DSources insertI1 insert_commute subset_trans)
    have "{ sA2 } \<subseteq> Sources level0 sA2"
      by (metis DSource_Sources DSourcesA2_L0 DSourcesA3_L0 
             DSourcesA4_L0 Sources_DSources insertI1 
             insert_commute subset_trans)
    with dsA4 show "{sA1, sA2, sA3, sA4} \<subseteq> Sources level0 sA2"
       by (metis DSourcesA2_L0 Sources_DSources insert_subset)
   qed
qed
        
lemma SourcesA3_L0: "Sources level0 sA3 = { sA1, sA2, sA3, sA4 }"
proof 
  show "Sources level0 sA3 \<subseteq> {sA1, sA2, sA3, sA4}"
  proof -
    have a2:"Sources level0 sA2 = { sA1, sA2, sA3, sA4}" by (simp add: SourcesA2_L0)
    have "{ sA2 } \<subseteq> DSources level0 sA3" by (simp add: DSourcesA3_L0)
    with a2 show "Sources level0 sA3 \<subseteq> {sA1, sA2, sA3, sA4}"
       by (metis DSource_Sources DSourcesA2_L0 DSourcesA4_L0 insertI1 insert_commute subset_trans)
  qed
next
   show "{sA1, sA2, sA3, sA4} \<subseteq> Sources level0 sA3"
   by (metis (full_types) DSource_Sources DSourcesA3_L0  SourcesA2_L0 insertI1)
qed    
             
lemma SourcesA4_L0: "Sources level0 sA4 = { sA1, sA2, sA3, sA4 }"
proof -
  have  A3s:"Sources level0 sA3 = { sA1, sA2, sA3, sA4 }" by (rule  SourcesA3_L0)
  have  "Sources level0 sA4 = {sA3} \<union> Sources level0 sA3"
    by (metis DSourcesA4_L0 Sources_singleDSource) 
  with A3s show ?thesis by auto
qed  

lemma SourcesA5_L0: "Sources level0 sA5 = { sA1, sA2, sA3, sA4 }"
proof -  
  have  A4s:"Sources level0 sA4 = { sA1, sA2, sA3, sA4 }" by (rule  SourcesA4_L0)
  have  "Sources level0 sA5 = {sA4} \<union> Sources level0 sA4"
    by (metis DSourcesA5_L0 Sources_singleDSource) 
  with A4s show ?thesis by auto
qed  

lemma SourcesA6_L0: "Sources level0 sA6 = {}"  
by (simp add: DSourcesA6_L0 DSourcesEmptySources) 

lemma SourcesA7_L0: "Sources level0 sA7 = { sA6 }"  
by (metis DSourcesA7_L0 SourcesA6_L0 SourcesEmptyDSources SourcesOnlyDSources singleton_iff)

 
lemma SourcesA8_L0: "Sources level0 sA8 = { sA6, sA7, sA8, sA9 }"  
proof - 
  have  dA8:"DSources level0 sA8 = {sA7, sA9}" by (rule DSourcesA8_L0)
  have  dA9:"DSources level0 sA9 = {sA8}" by (rule DSourcesA9_L0)
  have "(Sources level0 sA8) = (DSources level0 sA8) \<union> (\<Union> S \<in> (DSources level0 sA8). (Sources level0 S))" 
    by (rule SourcesDef)
  hence sourcesA8:"(Sources level0 sA8) = ({sA7, sA9, sA6} \<union> (Sources level0 sA9))" 
    by (simp add:  DSourcesA8_L0 SourcesA7_L0, auto)
  have "(Sources level0 sA9) = (DSources level0 sA9) \<union> (\<Union> S \<in> (DSources level0 sA9). (Sources level0 S))" 
    by (rule SourcesDef)
  hence "(Sources level0 sA9) = ({sA8} \<union> (Sources level0 sA8))" 
    by (simp add:  DSourcesA9_L0)
  with sourcesA8 have "(Sources level0 sA8) = {sA7, sA9, sA6} \<union> {sA8} \<union> {sA8, sA9}"
    by (metis SourcesLoop)  
  thus  ?thesis by auto
qed

lemma SourcesA9_L0: "Sources level0 sA9 = { sA6, sA7, sA8, sA9 }"  
proof - 
  have "(Sources level0 sA9) = (DSources level0 sA9) \<union> (\<Union> S \<in> (DSources level0 sA9). (Sources level0 S))" 
    by (rule SourcesDef)
  hence sourcesA9:"(Sources level0 sA9) = ({sA8} \<union> (Sources level0 sA8))" 
    by (simp add:  DSourcesA9_L0)
   thus ?thesis  by (metis SourcesA8_L0 Un_insert_right insert_absorb2 insert_is_Un) 
qed
 

\<comment> \<open>Abstraction level 1\<close>

lemma A12_NotSource_level1: "isNotDSource level1 sA12"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)

lemma A21_NotSource_level1: "isNotDSource level1 sA21"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)

lemma A5_NotSource_level1: "isNotDSource level1 sA5"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)

lemma A92_NotSource_level1: "isNotDSource level1 sA92"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)

lemma A93_NotSource_level1: "isNotDSource level1 sA93"
by (simp add: isNotDSource_def, auto,  case_tac "Z", auto)


lemma A11_DAcc_level1: "DAcc level1 sA11 = { sA21, sA22, sA23 }" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A12_DAcc_level1: "DAcc level1 sA12 = {}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A21_DAcc_level1: "DAcc level1 sA21 = {}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A22_DAcc_level1: "DAcc level1 sA22 = {sA31}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A23_DAcc_level1: "DAcc level1 sA23 = {sA32}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A31_DAcc_level1: "DAcc level1 sA31 = {sA41}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A32_DAcc_level1: "DAcc level1 sA32 = {sA41}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A41_DAcc_level1: "DAcc level1 sA41 = {sA22}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A42_DAcc_level1: "DAcc level1 sA42 = {sA5}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A5_DAcc_level1: "DAcc level1 sA5 = {}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A6_DAcc_level1: "DAcc level1 sA6 = {sA71, sA72}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A71_DAcc_level1: "DAcc level1 sA71 = {sA81}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A72_DAcc_level1: "DAcc level1 sA72 = {sA82}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A81_DAcc_level1: "DAcc level1 sA81 = {sA91, sA92}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A82_DAcc_level1: "DAcc level1 sA82 = {sA93}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A91_DAcc_level1: "DAcc level1 sA91 = {sA81}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A92_DAcc_level1: "DAcc level1 sA92 = {}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A93_DAcc_level1: "DAcc level1 sA93 = {}" 
by (simp add: DAcc_def  AbstrLevel1, auto)

lemma A42_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). C \<noteq> sA5 \<longrightarrow> sA42 \<notin> (Sources level1 C)"
by (metis A42_DAcc_level1 A5_NotSource_level1 singleDSourceEmpty4isNotSource)

lemma A5_NotSourceSet_level1 :
"\<forall> C  \<in> (AbstrLevel level1). sA5 \<notin> (Sources level1 C)"
by (metis A5_NotSource_level1 isNotSource_Sources)

lemma A92_NotSourceSet_level1 :
"\<forall> C  \<in> (AbstrLevel level1). sA92 \<notin> (Sources level1 C)" 
by (metis A92_NotSource_level1 isNotSource_Sources)

lemma A93_NotSourceSet_level1 :
"\<forall> C  \<in> (AbstrLevel level1). sA93 \<notin> (Sources level1 C)" 
by (metis A93_NotSource_level1 isNotSource_Sources)


lemma DSourcesA11_L1: "DSources level1 sA11 = {}"
by (simp add: DSources_def, auto, case_tac "x", auto) 

lemma DSourcesA12_L1: "DSources level1 sA12 = {}"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA21_L1: "DSources level1 sA21 = {sA11}"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA22_L1: "DSources level1 sA22 = {sA11, sA41}"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA23_L1: "DSources level1 sA23 = {sA11}"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA31_L1: "DSources level1 sA31 = { sA22 }"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA32_L1: "DSources level1 sA32 = { sA23 }"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA41_L1: "DSources level1 sA41 = { sA31, sA32 }"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA42_L1: "DSources level1 sA42 = {}"
by (simp add: DSources_def AbstrLevel1, auto) 

lemma DSourcesA5_L1: "DSources level1 sA5 = { sA42 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA6_L1: "DSources level1 sA6 = {}"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA71_L1: "DSources level1 sA71 = { sA6 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA72_L1: "DSources level1 sA72 = { sA6 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA81_L1: "DSources level1 sA81 = { sA71, sA91 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA82_L1: "DSources level1 sA82 = { sA72 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA91_L1: "DSources level1 sA91 = { sA81 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA92_L1: "DSources level1 sA92 = { sA81 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma DSourcesA93_L1: "DSources level1 sA93 = { sA82 }"
by (simp add: DSources_def AbstrLevel1, auto)  

lemma A82_Acc: "(Acc level1 sA82) = {sA93}"
by (metis A82_DAcc_level1 A93_NotSource_level1 singleDSourceEmpty_Acc) 

lemma A82_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA93 \<longrightarrow> sA82 \<notin> (Sources level1 C))"
by (metis A82_Acc Acc_Sources singleton_iff) 

lemma A72_Acc: "(Acc level1 sA72) = {sA82, sA93}"
proof -
  have daA72:  "DAcc level1 sA72 = { sA82 }"  by (rule A72_DAcc_level1)
  hence "(\<Union> S \<in> (DAcc level1 sA72). (Acc level1 S)) = (Acc level1 sA82)"  by simp
  hence aA72:"(\<Union> S \<in> (DAcc level1 sA72). (Acc level1 S)) = { sA93 }" by (simp add: A82_Acc)
  have "(Acc level1 sA72) = (DAcc level1 sA72) \<union> (\<Union> S \<in> (DAcc level1 sA72). (Acc level1 S))"  
    by (rule AccDef)
  with daA72 aA72 show ?thesis by auto
qed

lemma A72_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA93 \<and> C \<noteq> sA82 \<longrightarrow> sA72 \<notin> (Sources level1 C))"
by (metis A72_Acc Acc_Sources insert_iff singleton_iff) 

lemma A92_Acc: "(Acc level1 sA92) = {}"
by (metis A92_NotSource_level1 isNotDSource_EmptyAcc)

lemma A92_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (sA92 \<notin> (Sources level1 C))"
by (metis A92_NotSourceSet_level1)
 
lemma A91_Acc: "(Acc level1 sA91) = {sA81, sA91, sA92}"
proof -
  have da91:  "DAcc level1 sA91 = { sA81 }"  by (rule A91_DAcc_level1)
  hence a91:"(\<Union> S \<in> (DAcc level1 sA91). (Acc level1 S)) = (Acc level1 sA81)"  by simp
  have "(Acc level1 sA91) = (DAcc level1 sA91) \<union> (\<Union> S \<in> (DAcc level1 sA91). (Acc level1 S))"  by (rule AccDef)
  with da91 a91 have acc91:"(Acc level1 sA91) = { sA81 } \<union> (Acc level1 sA81)" by simp
  have da81:  "DAcc level1 sA81 = { sA91, sA92 }"  by (rule A81_DAcc_level1)
  hence a81:"(\<Union> S \<in> (DAcc level1 sA81). (Acc level1 S)) = (Acc level1 sA92) \<union> (Acc level1 sA91)"  by auto
  have "(Acc level1 sA81) = (DAcc level1 sA81) \<union> (\<Union> S \<in> (DAcc level1 sA81). (Acc level1 S))"  by (rule AccDef)
  with da81 a81 have acc81: "(Acc level1 sA81) = { sA91, sA92 }  \<union> (Acc level1 sA91)"
    by (metis A92_Acc sup_bot.left_neutral)
  from acc91 acc81 have "(Acc level1 sA91) = { sA81 } \<union> { sA91, sA92 }  \<union> {sA91, sA81}"
   by (metis AccLoop)
  thus ?thesis by auto
qed

lemma A91_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81 \<longrightarrow> sA91 \<notin> (Sources level1 C))"
proof -
  have "\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81  \<longrightarrow> (C \<notin> (Acc level1 sA91)))"
    by (metis A91_Acc insert_iff singleton_iff)
  thus ?thesis  by (metis Acc_SourcesNOT) 
qed

lemma A81_Acc: "(Acc level1 sA81) = {sA81, sA91, sA92}"
proof -
  have da91:  "DAcc level1 sA91 = { sA81 }"  by (rule A91_DAcc_level1)
  hence a91:"(\<Union> S \<in> (DAcc level1 sA91). (Acc level1 S)) = (Acc level1 sA81)"  by simp
  have "(Acc level1 sA91) = (DAcc level1 sA91) \<union> (\<Union> S \<in> (DAcc level1 sA91). (Acc level1 S))"  by (rule AccDef)
  with da91 a91 have acc91:"(Acc level1 sA91) = { sA81 } \<union> (Acc level1 sA81)" by simp
  have da81:  "DAcc level1 sA81 = { sA91, sA92 }"  by (rule A81_DAcc_level1)
  hence a81:"(\<Union> S \<in> (DAcc level1 sA81). (Acc level1 S)) = (Acc level1 sA92) \<union> (Acc level1 sA91)"  by auto
  have "(Acc level1 sA81) = (DAcc level1 sA81) \<union> (\<Union> S \<in> (DAcc level1 sA81). (Acc level1 S))"  by (rule AccDef)
  with da81 a81 have acc81: "(Acc level1 sA81) = { sA91, sA92 }  \<union> (Acc level1 sA91)"
    by (metis A92_Acc sup_bot.left_neutral)
  from acc81 acc91 have "(Acc level1 sA81) =  { sA91, sA92 }  \<union> { sA81 } \<union> {sA81, sA91}"
   by (metis AccLoop)
  thus ?thesis by auto
qed

lemma A81_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81 \<longrightarrow> sA81 \<notin> (Sources level1 C))"
proof -
  have "\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81  \<longrightarrow> (C \<notin> (Acc level1 sA81)))"
    by (metis A81_Acc insert_iff singleton_iff)
  thus ?thesis  by (metis Acc_SourcesNOT) 
qed

lemma A71_Acc: "(Acc level1 sA71) = {sA81, sA91, sA92}"
proof -
  have da71:  "DAcc level1 sA71 = { sA81 }"  by (rule A71_DAcc_level1)
  hence a71:"(\<Union> S \<in> (DAcc level1 sA71). (Acc level1 S)) = (Acc level1 sA81)"  by simp
  have "(Acc level1 sA71) = (DAcc level1 sA71) \<union> (\<Union> S \<in> (DAcc level1 sA71). (Acc level1 S))"  by (rule AccDef)
  with da71 a71 show ?thesis by (metis A91_Acc A91_DAcc_level1 AccDef) 
qed

lemma A71_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81 \<longrightarrow> sA71 \<notin> (Sources level1 C))"
proof -
  have "\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA81  \<longrightarrow> (C \<notin> (Acc level1 sA71)))"
    by (metis A71_Acc insert_iff singleton_iff)
  thus ?thesis  by (metis Acc_SourcesNOT) 
qed

lemma A6_Acc_L1:
"(Acc level1 sA6) = {sA71, sA72, sA81, sA82, sA91, sA92, sA93}"
proof -
  have daA6:  "DAcc level1 sA6 = { sA71, sA72 }"  by (rule A6_DAcc_level1)
  hence "(\<Union> S \<in> (DAcc level1 sA6). (Acc level1 S)) = (Acc level1 sA71) \<union> (Acc level1 sA72)"  by simp
  hence aA6:"(\<Union> S \<in> (DAcc level1 sA6). (Acc level1 S)) = {sA81, sA91, sA92} \<union> {sA82, sA93}" 
    by (simp add: A71_Acc A72_Acc)
  have "(Acc level1 sA6) = (DAcc level1 sA6) \<union> (\<Union> S \<in> (DAcc level1 sA6). (Acc level1 S))"  
    by (rule AccDef)
  with daA6 aA6 show ?thesis by auto
qed

lemma A6_NSources_L1Acc:
"\<forall> C \<in> (AbstrLevel level1). (C \<notin> (Acc level1 sA6) \<longrightarrow> sA6 \<notin> (Sources level1 C))"
by (metis Acc_SourcesNOT)


lemma A6_NSources_L1:
"\<forall> C \<in> (AbstrLevel level1). (C \<noteq> sA93 \<and> C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA82  \<and> C \<noteq> sA81 \<and> C \<noteq> sA72 \<and> C \<noteq> sA71 
\<longrightarrow> sA6 \<notin> (Sources level1 C))"
proof -
  have "\<forall> C \<in> (AbstrLevel level1). 
  (C \<noteq> sA93 \<and> C \<noteq> sA92 \<and> C \<noteq> sA91 \<and> C \<noteq> sA82  \<and> C \<noteq> sA81 \<and> C \<noteq> sA72 \<and> C \<noteq> sA71 
  \<longrightarrow> (C \<notin> (Acc level1 sA6)))"
     by (metis A6_Acc_L1 empty_iff insert_iff)
  thus ?thesis  by (metis Acc_SourcesNOT) 
qed

lemma A5_Acc_L1: "(Acc level1 sA5) = {}"
by (metis A5_NotSource_level1 isNotDSource_EmptyAcc)


lemma SourcesA11_L1: "Sources level1 sA11 = {}"  
by (simp add: DSourcesA11_L1 DSourcesEmptySources) 

lemma SourcesA12_L1: "Sources level1 sA12 = {}"  
by (simp add: DSourcesA12_L1  DSourcesEmptySources) 

lemma SourcesA21_L1: "Sources level1 sA21 = {sA11}"
by (simp add: DSourcesA21_L1 SourcesA11_L1  Sources_singleDSource) 

lemma SourcesA22_L1: "Sources level1 sA22 = {sA11, sA22,  sA23, sA31, sA32, sA41}"
proof
  show "Sources level1 sA22 \<subseteq> {sA11, sA22, sA23, sA31, sA32, sA41}"
  proof -
     have A2level1:"sA22 \<in> (AbstrLevel level1)" by (simp add: AbstrLevel1)
     from A2level1 have sgA42:"sA42 \<notin> Sources level1 sA22" by (metis A42_NSources_L1 CSet.distinct(347)) 
     have sgA5:"sA5 \<notin> Sources level1 sA22"
     by (metis A5_NotSource_level1 Acc_Sources all_not_in_conv isNotDSource_EmptyAcc)  
     have sgA12:"sA12 \<notin> Sources level1 sA22" by (metis A12_NotSource_level1 A2level1 isNotSource_Sources)   
     have sgA21:"sA21 \<notin> Sources level1 sA22"
     by (metis A21_NotSource_level1 DAcc_DSourcesNOT NDSourceExistsDSource empty_iff isNotDSource_EmptyDAcc)
     from A2level1 have sgA6:"sA6 \<notin> Sources level1 sA22" by (simp add: A6_NSources_L1)
     from A2level1 have sgA71:"sA71 \<notin> Sources level1 sA22" by (simp add: A71_NSources_L1)
     from A2level1 have sgA72:"sA72 \<notin> Sources level1 sA22" by (simp add: A72_NSources_L1)
     from A2level1 have sgA81:"sA81 \<notin> Sources level1 sA22" by (simp add: A81_NSources_L1)
     from A2level1 have sgA82:"sA82 \<notin> Sources level1 sA22" by (simp add: A82_NSources_L1)
     from A2level1 have sgA91:"sA91 \<notin> Sources level1 sA22" by (simp add: A91_NSources_L1)
     from A2level1 have sgA92:"sA92 \<notin> Sources level1 sA22" by (simp add: A92_NSources_L1) 
     from A2level1 have sgA93:"sA93 \<notin> Sources level1 sA22" by (metis A93_NotSourceSet_level1)  
     have "Sources level1 sA22 \<subseteq> {sA11, sA12, sA21, sA22, sA23, sA31, sA32, 
        sA41, sA42, sA5, sA6, sA71, sA72, sA81, sA82, sA91, sA92, sA93}"
        by (metis AbstrLevel1 SourcesLevelX) 
     with sgA5 sgA12 sgA21 sgA42 sgA6 sgA71 sgA72 sgA81 sgA82 sgA91 sgA92 sgA93 show 
     "Sources level1 sA22 \<subseteq> {sA11, sA22, sA23, sA31, sA32, sA41}"
         by auto 
    qed
next 
  show "{sA11, sA22, sA23, sA31, sA32, sA41} \<subseteq> Sources level1 sA22" 
  proof - 
    have sDef:"(Sources level1 sA22) = (DSources level1 sA22) \<union> (\<Union> S \<in> (DSources level1 sA22). (Sources level1 S))" 
       by (rule SourcesDef) 
    have A11s: "sA11 \<in> Sources level1 sA22" by (metis DSourceIsSource DSourcesA22_L1 insertI1)  
    have A41s: "sA41 \<in> Sources level1 sA22" by (metis (full_types) DSourceIsSource DSourcesA22_L1 insertCI)
    have A31s: "sA31 \<in> Sources level1 sA22" 
      by (metis (full_types) A41s DSourceIsSource DSourcesA41_L1 SourcesTrans insertCI)
    have A32s: "sA32 \<in> Sources level1 sA22"
      by (metis A32_DAcc_level1 A41s DAcc_DSourcesNOT DSourceOfSource insertI1)
    have A23s: "sA23 \<in> Sources level1 sA22"  by (metis A32s DSourceOfSource DSourcesA32_L1 insertI1)
    have A22s: "sA22 \<in> Sources level1 sA22"  by (metis A31s DSourceOfSource DSourcesA31_L1 insertI1)
    with A11s A22s A23s A31s A32s A41s show ?thesis by auto
    qed
qed 

lemma SourcesA23_L1: "Sources level1 sA23 = {sA11}"
by (simp add: DSourcesA23_L1 SourcesA11_L1  Sources_singleDSource)  

lemma SourcesA31_L1: "Sources level1 sA31 = {sA11, sA22, sA23, sA31, sA32, sA41}"
by (metis DSourcesA31_L1 SourcesA22_L1 Sources_singleDSource Un_insert_right insert_absorb2 insert_is_Un)

lemma SourcesA32_L1: "Sources level1 sA32 = {sA11, sA23}"
by (metis DSourcesA32_L1 SourcesA23_L1 Sources_singleDSource Un_insert_right insert_is_Un)
 
lemma SourcesA41_L1: "Sources level1 sA41 = {sA11, sA22, sA23, sA31, sA32, sA41}"
by (metis DSourcesA41_L1 SourcesA31_L1 SourcesA32_L1 Sources_2DSources Un_absorb Un_commute Un_insert_left)

lemma SourcesA42_L1: "Sources level1 sA42 = {}"  
by (simp add: DSourcesA42_L1  DSourcesEmptySources) 

lemma SourcesA5_L1: "Sources level1 sA5 = {sA42}"
by (simp add: DSourcesA5_L1 SourcesA42_L1  Sources_singleDSource) 

lemma SourcesA6_L1: "Sources level1 sA6 = {}"  
by (simp add: DSourcesA6_L1 DSourcesEmptySources) 

lemma SourcesA71_L1: "Sources level1 sA71 = {sA6}"
by (metis DSourcesA71_L1 SourcesA6_L1 SourcesEmptyDSources SourcesOnlyDSources singleton_iff)   

lemma SourcesA81_L1: "Sources level1 sA81 = {sA6, sA71, sA81, sA91}"  
proof - 
  have  dA81:"DSources level1 sA81 = {sA71, sA91}" by (rule DSourcesA81_L1)
  have  dA91:"DSources level1 sA91 = {sA81}" by (rule DSourcesA91_L1)
  have "(Sources level1 sA81) = (DSources level1 sA81) \<union> (\<Union> S \<in> (DSources level1 sA81). (Sources level1 S))" 
    by (rule SourcesDef)
  with dA81 have  "(Sources level1 sA81) = ({sA71, sA91} \<union> (Sources level1 sA71) \<union> (Sources level1 sA91))"
    by (metis (hide_lams, no_types) SUP_empty UN_insert Un_insert_left sup_bot.left_neutral sup_commute)
  hence sourcesA81:"(Sources level1 sA81) = ({sA71, sA91, sA6} \<union> (Sources level1 sA91))"
    by (metis SourcesA71_L1 insert_is_Un sup_assoc)
  have "(Sources level1 sA91) = (DSources level1 sA91) \<union> (\<Union> S \<in> (DSources level1 sA91). (Sources level1 S))" 
    by (rule SourcesDef)
  with dA91 have "(Sources level1 sA91) = ({sA81} \<union> (Sources level1 sA81))"  by simp
  with sourcesA81 have "(Sources level1 sA81) = {sA71, sA91, sA6} \<union> {sA81} \<union> {sA81, sA91}"
    by (metis SourcesLoop)  
  thus  ?thesis by auto
qed

(*lemma Sources_singleDSource:
  assumes "DSources i S = {C}" 
  shows    "Sources i S = {C} \<union> Sources i C" *)
lemma SourcesA91_L1: "Sources level1 sA91 = {sA6, sA71, sA81, sA91}"
proof -
  have  "DSources level1 sA91 = {sA81}" by (rule DSourcesA91_L1)
  thus ?thesis by (metis SourcesA81_L1 Sources_singleDSource 
          Un_empty_left Un_insert_left insert_absorb2 insert_commute) 
qed

lemma SourcesA92_L1: "Sources level1 sA92 = {sA6, sA71, sA81, sA91}"
by (metis DSourcesA91_L1 DSourcesA92_L1 SourcesA91_L1 Sources_singleDSource) 

lemma SourcesA72_L1: "Sources level1 sA72 = {sA6}"
by (metis DSourcesA6_L1 DSourcesA72_L1 SourcesOnlyDSources singleton_iff)   

lemma SourcesA82_L1: "Sources level1 sA82 = {sA6, sA72}"  
proof - 
  have  dA82:"DSources level1 sA82 = {sA72}" by (rule DSourcesA82_L1)
  have "(Sources level1 sA82) = (DSources level1 sA82) \<union> (\<Union> S \<in> (DSources level1 sA82). (Sources level1 S))" 
    by (rule SourcesDef)
  with dA82 have "(Sources level1 sA82) =  {sA72} \<union> (Sources level1 sA72)"  by simp
  thus ?thesis by (metis SourcesA72_L1 Un_commute insert_is_Un) 
qed

lemma SourcesA93_L1: "Sources level1 sA93 = {sA6, sA72, sA82}"
by (metis DSourcesA93_L1 SourcesA82_L1 Sources_singleDSource Un_insert_right insert_is_Un)   


\<comment> \<open>Abstraction level 2\<close>

lemma SourcesS1_L2: "Sources level2 sS1 = {}"
proof -
  have "DSources level2 sS1 = {}"  by (simp add: DSources_def AbstrLevel2, auto)
  thus ?thesis  by (simp add: DSourcesEmptySources)
qed

lemma SourcesS2_L2: "Sources level2 sS2 = {}"
proof -
  have "DSources level2 sS2 = {}"  by (simp add: DSources_def AbstrLevel2, auto)
  thus ?thesis  by (simp add: DSourcesEmptySources)
qed

lemma SourcesS3_L2: "Sources level2 sS3 = {sS2}"
proof -
  have DSourcesS3:"DSources level2 sS3 = {sS2}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS2 = {}"  by (rule SourcesS2_L2)
  with DSourcesS3 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS4_L2:  "Sources level2 sS4 = {sS2}"
proof -
  have DSourcesS4:"DSources level2 sS4 = {sS2}" by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS2 = {}"  by (rule SourcesS2_L2)
  with DSourcesS4 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS5_L2:  "Sources level2 sS5 = {sS2, sS4}"
proof -
  have DSourcesS5:"DSources level2 sS5 = {sS4}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS4 = {sS2}" by (rule SourcesS4_L2)
  with DSourcesS5 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS6_L2:  "Sources level2 sS6 = {sS2, sS4, sS5}"
proof -
  have DSourcesS6:"DSources level2 sS6 = {sS2, sS5}"  by (simp add: DSources_def AbstrLevel2, auto)
  have SourcesS2:"Sources level2 sS2 = {}"  by (rule SourcesS2_L2)
  have "Sources level2 sS5 = {sS2, sS4}"  by (rule SourcesS5_L2)
  with  SourcesS2 DSourcesS6 show ?thesis  by (simp add: Sources_2DSources, auto)
qed

lemma SourcesS7_L2:  "Sources level2 sS7 = {}"
proof -
  have "DSources level2 sS7 = {}"  by (simp add: DSources_def AbstrLevel2, auto)
  thus ?thesis  by (simp add: DSourcesEmptySources)
qed

lemma SourcesS8_L2:
 "Sources level2 sS8 = {sS7}"
proof -
  have DSourcesS8:"DSources level2 sS8 = {sS7}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS7 = {}"  by (rule SourcesS7_L2)
  with DSourcesS8 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS9_L2:
 "Sources level2 sS9 = {}"
proof -
  have "DSources level2 sS9 = {}"  by (simp add: DSources_def AbstrLevel2, auto)
  thus ?thesis  by (simp add: DSourcesEmptySources)
qed

lemma SourcesS10_L2: "Sources level2 sS10 = {sS9}"
proof -
  have DSourcesS10:"DSources level2 sS10 = {sS9}" by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS9 = {}" by (rule SourcesS9_L2)
  with DSourcesS10 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS11_L2: "Sources level2 sS11 = {sS9}"
proof -
  have DSourcesS11:"DSources level2 sS11 = {sS9}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS9 = {}"  by (rule SourcesS9_L2)
  with DSourcesS11 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS12_L2: "Sources level2 sS12 = {sS9, sS10}"
proof -
  have DSourcesS12:"DSources level2 sS12 = {sS10}" by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS10 = {sS9}"  by (rule SourcesS10_L2)
  with DSourcesS12 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS13_L2: "Sources level2 sS13 = {sS9, sS10, sS12}"
proof -
  have DSourcesS13:"DSources level2 sS13 = {sS12}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS12 = {sS9, sS10}" by (rule SourcesS12_L2)
  with DSourcesS13 show ?thesis by  (simp add: Sources_singleDSource)
qed

lemma SourcesS14_L2: "Sources level2 sS14 = {sS9, sS11}"
proof -
  have DSourcesS14:"DSources level2 sS14 = {sS11}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS11 = {sS9}"  by (rule SourcesS11_L2)
  with DSourcesS14 show ?thesis  by  (simp add: Sources_singleDSource)
qed

lemma SourcesS15_L2: "Sources level2 sS15 = {sS9, sS11, sS14}"
proof -
  have DSourcesS15:"DSources level2 sS15= {sS14}"  by (simp add: DSources_def AbstrLevel2, auto)
  have "Sources level2 sS14 = {sS9, sS11}"  by (rule SourcesS14_L2)
  with DSourcesS15 show ?thesis by  (simp add: Sources_singleDSource)
qed


subsection \<open>Minimal sets of components to prove certain properties\<close>

lemma minSetOfComponentsTestL2p1:
"minSetOfComponents level2 {data10, data13} = {sS1}"
proof - 
  have outL2:"outSetOfComponents level2 {data10, data13} = {sS1}"
    by (simp add: outSetOfComponents_def  AbstrLevel2, auto) 
  have "Sources level2 sS1 = {}" by (simp add: SourcesS1_L2)
  with outL2 show ?thesis by (simp add:  minSetOfComponents_def)
qed

lemma NOT_noIrrelevantChannelsTestL2p1:
" \<not> noIrrelevantChannels level2 {data10, data13}"
by (simp add: noIrrelevantChannels_def systemIN_def minSetOfComponentsTestL2p1 AbstrLevel2)

lemma NOT_allNeededINChannelsTestL2p1:
"\<not> allNeededINChannels  level2 {data10, data13}"
by (simp add: allNeededINChannels_def minSetOfComponentsTestL2p1  systemIN_def AbstrLevel2)

lemma minSetOfComponentsTestL2p2:
"minSetOfComponents level2 {data1, data12} = {sS2, sS4, sS5, sS6}"
proof - 
  have outL2:"outSetOfComponents level2 {data1, data12} = {sS6}"
    by (simp add: outSetOfComponents_def  AbstrLevel2, auto) 
  have "Sources level2 sS6 = {sS2, sS4, sS5}"
    by  (simp add: SourcesS6_L2) 
  with outL2 show ?thesis 
    by (simp add:  minSetOfComponents_def) 
qed
 
lemma noIrrelevantChannelsTestL2p2:
"noIrrelevantChannels level2  {data1, data12}"
by (simp add: noIrrelevantChannels_def systemIN_def minSetOfComponentsTestL2p2 AbstrLevel2)

lemma allNeededINChannelsTestL2p2:
"allNeededINChannels  level2 {data1, data12}"
by (simp add: allNeededINChannels_def minSetOfComponentsTestL2p2  systemIN_def AbstrLevel2)

lemma minSetOfComponentsTestL1p3:
"minSetOfComponents level1 {data1, data10, data11} = {sA12, sA11, sA21}"
proof - 
  have sg1:"outSetOfComponents level1 {data1, data10, data11} = {sA12, sA21}"
    by (simp add: outSetOfComponents_def  AbstrLevel1, auto)  
  have "DSources level1 sA12 = {}"
    by (simp add: DSources_def AbstrLevel1, auto) 
  hence sg2:"Sources level1 sA12 = {}"
    by (simp add: DSourcesEmptySources)  
  have sg3:"DSources level1 sA21 = {sA11}"
    by (simp add: DSources_def AbstrLevel1, auto) 
  have sg4:"DSources level1 sA11 = {}"
    by (simp add: DSources_def AbstrLevel1, auto)  
  hence "Sources level1 sA21 = {sA11}"
    by (metis SourcesOnlyDSources sg3 singleton_iff)
  from this and sg1 and sg2 show ?thesis
     by (simp add:  minSetOfComponents_def, blast) 
qed

lemma noIrrelevantChannelsTestL1p3:
"noIrrelevantChannels level1  {data1, data10, data11}"
by (simp add: noIrrelevantChannels_def systemIN_def minSetOfComponentsTestL1p3 AbstrLevel1)

lemma allNeededINChannelsTestL1p3:
"allNeededINChannels  level1 {data1, data10, data11}"
by (simp add: allNeededINChannels_def minSetOfComponentsTestL1p3  systemIN_def AbstrLevel1)

lemma minSetOfComponentsTestL2p3:
"minSetOfComponents level2 {data1, data10, data11} = {sS1, sS2, sS3}"
proof - 
  have sg1:"outSetOfComponents level2 {data1, data10, data11} = {sS1, sS3}"
    by (simp add: outSetOfComponents_def  AbstrLevel2, auto)  
  have sS1:"Sources level2 sS1 = {}" by (simp add: SourcesS1_L2)
  have "Sources level2 sS3 = {sS2}" by (simp add: SourcesS3_L2)
   with sg1 sS1 show ?thesis
     by (simp add:  minSetOfComponents_def, blast) 
qed
 
lemma noIrrelevantChannelsTestL2p3:
"noIrrelevantChannels level2  {data1, data10, data11}"
by (simp add: noIrrelevantChannels_def systemIN_def minSetOfComponentsTestL2p3 AbstrLevel2)

lemma allNeededINChannelsTestL2p3:
"allNeededINChannels  level2 {data1, data10, data11}"
by (simp add: allNeededINChannels_def minSetOfComponentsTestL2p3  systemIN_def AbstrLevel2)

end
