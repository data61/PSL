(*<*)
(*
   Title:  Theory  DataDependencies.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
(*>*)

section "Inter-/Intracomponent dependencies"
 
theory DataDependencies
  imports DataDependenciesConcreteValues
begin

\<comment> \<open>component and its subcomponents should be defined on different abstraction levels\<close>
definition
correctCompositionDiffLevels :: "CSet \<Rightarrow> bool"
where 
  "correctCompositionDiffLevels S \<equiv> 
   \<forall> C \<in>  subcomp S. \<forall> i. S \<in> AbstrLevel i \<longrightarrow> C \<notin> AbstrLevel i"

\<comment> \<open>General system's property: for all abstraction levels and all components should hold\<close>
\<comment> \<open>component and its subcomponents should be defined on different abstraction levels\<close>
definition
correctCompositionDiffLevelsSYSTEM :: "bool"
where 
  "correctCompositionDiffLevelsSYSTEM \<equiv> 
   (\<forall> S::CSet. (correctCompositionDiffLevels S))"

\<comment> \<open>if a local variable belongs to one of the subcomponents, it also belongs to the composed component\<close>
definition
correctCompositionVAR ::  "CSet \<Rightarrow> bool"
where
  "correctCompositionVAR S \<equiv> 
   \<forall> C \<in>  subcomp S. \<forall> v \<in> VAR C.  v \<in> VAR S"

\<comment> \<open>General system's property: for all abstraction levels and all components should hold\<close>
\<comment> \<open>if a local variable belongs to one of the subcomponents, it also belongs to the composed component\<close>
definition
correctCompositionVARSYSTEM ::  "bool"
where
  "correctCompositionVARSYSTEM \<equiv> 
   (\<forall> S::CSet. (correctCompositionVAR S))"

\<comment> \<open>after correct decomposition of a component each of its local variable can belong only to one of its subcomponents\<close>
definition
correctDeCompositionVAR ::  "CSet \<Rightarrow> bool"
where
  "correctDeCompositionVAR S \<equiv> 
   \<forall> v \<in> VAR S.  \<forall> C1 \<in>  subcomp S. \<forall> C2 \<in>  subcomp S. v \<in> VAR C1 \<and> v \<in> VAR C2 \<longrightarrow> C1 = C2"

\<comment> \<open>General system's property: for all abstraction levels and all components should hold\<close>
\<comment> \<open>after correct decomposition of a component each of its local variable can belong only to one of its subcomponents\<close>
definition
correctDeCompositionVARSYSTEM ::  "bool"
where
  "correctDeCompositionVARSYSTEM \<equiv> 
  (\<forall> S::CSet. (correctDeCompositionVAR S))"

\<comment> \<open>if x is an output channel of a  component C on some anstraction level, 
it cannot be an output of another component on the same level\<close>
definition
correctCompositionOUT ::  "chanID \<Rightarrow> bool"
where
  "correctCompositionOUT x \<equiv> 
   \<forall> C i. x \<in> OUT C \<and> C \<in> AbstrLevel i \<longrightarrow>  (\<forall> S \<in> AbstrLevel i. x \<notin> OUT S)"

\<comment> \<open>General system's property: for all abstraction levels and all channels should hold\<close>
definition
correctCompositionOUTSYSTEM ::  "bool"
where
  "correctCompositionOUTSYSTEM \<equiv> (\<forall> x. correctCompositionOUT x)"

\<comment> \<open>if X is a subcomponent of a  component C on some anstraction level, 
it cannot be a subcomponent of another component on the same level\<close>
definition
correctCompositionSubcomp ::  "CSet \<Rightarrow> bool"
where
  "correctCompositionSubcomp X \<equiv> 
   \<forall> C i. X \<in> subcomp C \<and> C \<in> AbstrLevel i \<longrightarrow>  (\<forall> S \<in> AbstrLevel i. (S \<noteq> C \<longrightarrow> X \<notin> subcomp S))"

\<comment> \<open>General system's property: for all abstraction levels and all components should hold\<close>
definition
correctCompositionSubcompSYSTEM ::  "bool"
where
  "correctCompositionSubcompSYSTEM \<equiv> (\<forall> X. correctCompositionSubcomp X)"

\<comment> \<open>If a component belongs is defined in the set CSet, 
it should belong to at least one abstraction level\<close>
definition
allComponentsUsed ::  "bool"
where
  "allComponentsUsed \<equiv>  \<forall> C. \<exists> i.  C \<in> AbstrLevel i"

\<comment> \<open>if a component does not have any local variables, none of its subcomponents has any local variables\<close>
lemma correctDeCompositionVARempty:
  assumes "correctCompositionVAR S" 
          and "VAR S = {}"
  shows    "\<forall> C \<in>  subcomp S. VAR C = {}"
using assms by (metis all_not_in_conv correctCompositionVAR_def)


\<comment> \<open>function OUTfrom maps channel ID to the set of input channels it depends from,\<close>
\<comment> \<open>directly (OUTfromCh) or via local variables (VARfrom)\<close> 
\<comment> \<open>an empty set means that the channel is either input of the system or\<close>
\<comment> \<open>its values are generated within some component independently\<close>
definition OUTfrom ::  "chanID \<Rightarrow> chanID set"
where
 "OUTfrom x \<equiv> (OUTfromCh x) \<union> {y. \<exists> v. v \<in> (OUTfromV x) \<and> y \<in> (VARfrom v)}"
 
\<comment> \<open>if x depends from some input channel(s) directly, then exists\<close>
\<comment> \<open>a component which has them as input channels and x as an output channel\<close>
definition
  OUTfromChCorrect :: "chanID \<Rightarrow> bool"
where
  "OUTfromChCorrect x \<equiv>
   (OUTfromCh x \<noteq> {} \<longrightarrow> 
      (\<exists> Z . (x \<in> (OUT Z) \<and> (\<forall> y \<in> (OUTfromCh x). y \<in> IN Z) )))"

\<comment> \<open>General system's property: for channels in the system should hold:\<close>
\<comment> \<open>if x depends from some input channel(s) directly, then exists\<close>
\<comment> \<open>a component which has them as input channels and x as an output channel\<close>
definition
  OUTfromChCorrectSYSTEM :: "bool"
where
  "OUTfromChCorrectSYSTEM \<equiv> (\<forall> x::chanID. (OUTfromChCorrect x))"


\<comment> \<open>if x depends from some local variables, then exists a component\<close>
\<comment> \<open>to which these variables belong and which has  x as an output channel\<close>
definition
  OUTfromVCorrect1 :: "chanID \<Rightarrow> bool"
where
  "OUTfromVCorrect1 x \<equiv>
   (OUTfromV x \<noteq> {} \<longrightarrow> 
      (\<exists> Z . (x \<in> (OUT Z) \<and> (\<forall> v \<in> (OUTfromV x). v \<in> VAR Z) )))"

\<comment> \<open>General system's property: for channels in the system should hold the above property:\<close>
definition
  OUTfromVCorrect1SYSTEM :: "bool"
where
  "OUTfromVCorrect1SYSTEM \<equiv> (\<forall> x::chanID. (OUTfromVCorrect1 x))"

\<comment> \<open>if x does not depend from any local variables, then it does not belong to any set VARfrom\<close>
definition
  OUTfromVCorrect2 :: "chanID \<Rightarrow> bool"
where
  "OUTfromVCorrect2 x \<equiv>
   (OUTfromV x = {} \<longrightarrow> (\<forall> v::varID. x \<notin> (VARto v)) )"

\<comment> \<open>General system's property: for channels in the system should hold the above property:\<close> 
definition
  OUTfromVCorrect2SYSTEM :: "bool"
where
  "OUTfromVCorrect2SYSTEM \<equiv>  (\<forall> x::chanID. (OUTfromVCorrect2 x))"

\<comment> \<open>General system's property:\<close>
\<comment> \<open>definitions OUTfromV and VARto should give equivalent mappings\<close>
definition
  OUTfromV_VARto :: "bool"
where
  "OUTfromV_VARto \<equiv>
   (\<forall> x::chanID. \<forall> v::varID. (v \<in> OUTfromV x \<longleftrightarrow> x \<in> (VARto v)) )"

\<comment> \<open>General system's property for abstraction levels 0 and 1\<close>
\<comment> \<open>if a variable v belongs to a component, then all the channels v\<close>
\<comment> \<open>depends from should be input channels of this component\<close>
definition
  VARfromCorrectSYSTEM :: "bool"
where
  "VARfromCorrectSYSTEM \<equiv>
   (\<forall> v::varID. \<forall> Z\<in> ((AbstrLevel level0) \<union> (AbstrLevel level1)). 
     ( (v \<in> VAR Z) \<longrightarrow>  (\<forall> x \<in> VARfrom v. x \<in> IN Z) ))"

\<comment> \<open>General system's property for abstraction levels 0 and 1\<close>
\<comment> \<open>if a variable v belongs to a component, then all the channels v\<close>
\<comment> \<open>provides value to should be input channels of this component\<close>
definition
  VARtoCorrectSYSTEM :: "bool"
where
  "VARtoCorrectSYSTEM \<equiv>
   (\<forall> v::varID. \<forall> Z \<in> ((AbstrLevel level0) \<union> (AbstrLevel level1)). 
     ( (v \<in> VAR Z) \<longrightarrow>   (\<forall> x \<in> VARto v. x \<in> OUT Z)))"

\<comment> \<open>to detect local variables, unused for computation of any output\<close> 
definition
  VARusefulSYSTEM :: "bool"
where
  "VARusefulSYSTEM \<equiv> (\<forall> v::varID. (VARto v \<noteq> {}))"

lemma
  OUTfromV_VARto_lemma: 
 assumes "OUTfromV x \<noteq> {}"  and "OUTfromV_VARto"
 shows    "\<exists> v::varID. x \<in> (VARto v)" 
 using assms by (simp add: OUTfromV_VARto_def, auto)

(*<*)
(*>*)
subsection \<open>Direct and indirect data dependencies between components\<close>

\<comment> \<open>The component C should be defined on the same abstraction\<close>
\<comment> \<open>level we are seaching for its direct or indirect sources,\<close>
\<comment> \<open>otherwise we get an empty set as result\<close>
definition
  DSources :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> CSet set"
where
 "DSources i C \<equiv> {Z.  \<exists> x. x \<in> (IN C) \<and> x \<in> (OUT Z) \<and> Z \<in> (AbstrLevel i) \<and> C \<in> (AbstrLevel i)}"

lemma DSourcesLevelX:
"(DSources i X)  \<subseteq> (AbstrLevel i)" 
by (simp add: DSources_def, auto)

\<comment> \<open>The component C should be defined on the same abstraction level we are\<close> 
\<comment> \<open>seaching for its direct or indirect acceptors (coponents, for which C is a source),\<close>
\<comment> \<open>otherwise we get an empty set as result\<close>
definition
  DAcc :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> CSet set"
where
 "DAcc i C \<equiv> {Z.  \<exists> x. x \<in> (OUT C) \<and> x \<in> (IN Z) \<and> Z \<in> (AbstrLevel i) \<and> C \<in> (AbstrLevel i)}"

axiomatization
  Sources :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> CSet set"
where 
SourcesDef:
"(Sources i C) = (DSources i C) \<union> (\<Union> S \<in> (DSources i C). (Sources i S))" 
and
SourceExistsDSource:
"S \<in> (Sources i C) \<longrightarrow> (\<exists> Z. S \<in> (DSources i Z))"
and
NDSourceExistsDSource:
"S \<in> (Sources i C) \<and> S \<notin> (DSources i C) \<longrightarrow> 
 (\<exists> Z. S \<in> (DSources i Z) \<and> Z \<in> (Sources i C))"
and
SourcesTrans:
"(C \<in> Sources i S \<and> S \<in> Sources i Z) \<longrightarrow> C \<in> Sources i Z"
and 
SourcesLevelX:
"(Sources i X)  \<subseteq> (AbstrLevel i)" 
and
SourcesLoop:
"(Sources i C) = (XS \<union> (Sources i S)) \<and> (Sources i S) = (ZS \<union> (Sources i C)) 
\<longrightarrow> (Sources i C) = XS  \<union> ZS \<union> { C, S}" 
\<comment> \<open>if we have a loop in the dependencies we need to cut it for counting the sources\<close>

axiomatization
  Acc :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> CSet set"
where 
AccDef:
"(Acc i C) = (DAcc i C) \<union> (\<Union> S \<in> (DAcc i C). (Acc i S))" 
and
Acc_Sources:
"(X \<in> Acc i C) = (C \<in> Sources i X)"
and
AccSigleLoop:
"DAcc i C = {S} \<and> DAcc i S = {C} \<longrightarrow> Acc i C = {C, S}" 
and
AccLoop:
"(Acc i C) = (XS \<union> (Acc i S)) \<and> (Acc i S) = (ZS \<union> (Acc i C)) 
\<longrightarrow> (Acc i C) = XS  \<union> ZS \<union> { C, S}" 
\<comment> \<open>if we have a loop in the dependencies we need to cut it for counting the accessors\<close>

lemma Acc_SourcesNOT: "(X \<notin> Acc i C) = (C \<notin> Sources i X)"
by (metis Acc_Sources)

\<comment> \<open>component S is not a source for any component on the abstraction level i\<close>
definition
  isNotDSource :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> bool"
where
 "isNotDSource i S \<equiv> (\<forall> x \<in> (OUT S). (\<forall> Z \<in> (AbstrLevel i). (x \<notin> (IN Z))))"

\<comment> \<open>component S is not a source for a component Z on the abstraction level i\<close>
definition
  isNotDSourceX :: "AbstrLevelsID \<Rightarrow> CSet \<Rightarrow> CSet \<Rightarrow> bool"
where
 "isNotDSourceX i S C \<equiv> (\<forall> x \<in> (OUT S). (C \<notin> (AbstrLevel i) \<or> (x \<notin> (IN C))))"

lemma isNotSource_isNotSourceX:
"isNotDSource i S = (\<forall> C. isNotDSourceX i S C)" 
by (auto, (simp add: isNotDSource_def isNotDSourceX_def)+)

lemma DAcc_DSources:
"(X \<in> DAcc i C) = (C \<in> DSources i X)"
by (auto, (simp add: DAcc_def DSources_def, auto)+)
 
lemma DAcc_DSourcesNOT:
"(X \<notin> DAcc i C) = (C \<notin> DSources i X)"
by (auto, (simp add: DAcc_def DSources_def, auto)+)

lemma DSource_level:
  assumes "S \<in> (DSources i C)"
  shows    "C  \<in> (AbstrLevel i)"
using assms by (simp add: DSources_def, auto)

lemma SourceExistsDSource_level:
  assumes "S \<in> (Sources i C)"
  shows    "\<exists> Z  \<in> (AbstrLevel i). (S \<in> (DSources i Z))"
using assms by (metis DSource_level SourceExistsDSource) 
  
lemma Sources_DSources:
 "(DSources i C) \<subseteq> (Sources i C)"   
proof -  
  have "(Sources i C) = (DSources i C) \<union> (\<Union> S \<in> (DSources i C). (Sources i S))" 
    by (rule SourcesDef)
  thus ?thesis by auto
qed

lemma NoDSourceNoSource:
  assumes "S \<notin> (Sources i C)"
  shows     "S \<notin> (DSources i C)"
using assms by (metis (full_types) Sources_DSources rev_subsetD)

lemma DSourcesEmptySources:
  assumes "DSources i C = {}"
  shows    "Sources i C = {}" 
proof - 
  have "(Sources i C) = (DSources i C) \<union> (\<Union> S \<in> (DSources i C). (Sources i S))"  
    by (rule SourcesDef) 
  with assms show ?thesis by auto
qed

lemma DSource_Sources:
  assumes  "S \<in> (DSources i C)"
  shows     "(Sources i S)  \<subseteq> (Sources i C)"
proof - 
 have  "(Sources i C) = (DSources i C) \<union> (\<Union> S \<in> (DSources i C). (Sources i S))"
  by (rule SourcesDef)
  with assms show ?thesis by auto
qed

lemma SourcesOnlyDSources:
  assumes "\<forall> X. (X \<in> (DSources i C) \<longrightarrow> (DSources i X) = {})"
  shows    "Sources i C = DSources i C"
proof - 
 have sDef:  "(Sources i C) = (DSources i C) \<union> (\<Union> S \<in> (DSources i C). (Sources i S))"
  by (rule SourcesDef)
 from assms have  "\<forall> X. (X \<in> (DSources i C) \<longrightarrow> (Sources i X) = {})"
   by (simp add: DSourcesEmptySources)
 hence "(\<Union> S \<in> (DSources i C). (Sources i S)) = {}"  by auto
 with sDef  show ?thesis by simp
qed

lemma SourcesEmptyDSources:
 assumes "Sources i C = {}"
 shows "DSources i C = {}"
using assms  by (metis Sources_DSources bot.extremum_uniqueI)

lemma NotDSource:
 assumes "\<forall> x \<in> (OUT S). (\<forall> Z \<in> (AbstrLevel i). (x \<notin> (IN Z)))"
 shows    "\<forall> C \<in> (AbstrLevel i) . S \<notin> (DSources i C)" 
using assms  by (simp add: AbstrLevel0 DSources_def) 

lemma allNotDSource_NotSource:
 assumes "\<forall> C . S \<notin> (DSources i C)" 
 shows    "\<forall> Z. S \<notin> (Sources i Z)" 
using assms  by (metis SourceExistsDSource) 

lemma NotDSource_NotSource:
 assumes "\<forall> C \<in> (AbstrLevel i). S \<notin> (DSources i C)" 
 shows    "\<forall> Z \<in> (AbstrLevel i). S \<notin> (Sources i Z)" 
using assms by (metis SourceExistsDSource_level)  

lemma isNotSource_Sources: 
 assumes "isNotDSource i S"
 shows "\<forall> C  \<in> (AbstrLevel i). S \<notin> (Sources i C)" 
using assms  
by (simp add: isNotDSource_def, metis (full_types) NotDSource NotDSource_NotSource)

lemma SourcesAbstrLevel:
assumes "x \<in> Sources i S"
shows "x \<in> AbstrLevel i"
using assms
by (metis SourcesLevelX in_mono)

lemma DSourceIsSource:
  assumes  "C \<in> DSources i S" 
     shows  "C \<in> Sources i S" 
proof -
  have "(Sources i S) = (DSources i S) \<union> (\<Union> Z \<in> (DSources i S). (Sources i Z))" 
    by (rule SourcesDef)
  with assms show ?thesis  by simp
qed

lemma DSourceOfDSource:
  assumes  "Z \<in> DSources i S" 
         and  "S \<in> DSources i C"
  shows     "Z \<in> Sources i C"
using assms
proof -
  from assms have src:"Sources i S \<subseteq> Sources i C" by (simp add: DSource_Sources)
  from assms have  "Z \<in> Sources i S"  by (simp add: DSourceIsSource)
  with src   show ?thesis  by auto
qed

lemma SourceOfDSource:
  assumes  "Z \<in> Sources i S" 
         and  "S \<in> DSources i C"
  shows     "Z \<in> Sources i C"
using assms
proof -
  from assms have "Sources i S \<subseteq> Sources i C" by (simp add: DSource_Sources) 
  thus ?thesis by (metis (full_types) assms(1) rev_subsetD)  
qed

lemma DSourceOfSource:
  assumes  cDS:"C \<in> DSources i S" 
         and  sS:"S \<in> Sources i Z"  
  shows     "C \<in> Sources i Z"
proof -
  from cDS have  "C \<in> Sources i S"  by (simp add: DSourceIsSource)
  from this and sS show ?thesis by (metis (full_types) SourcesTrans)  
qed

lemma Sources_singleDSource:
  assumes "DSources i S = {C}" 
  shows    "Sources i S = {C} \<union> Sources i C"
proof - 
 have sDef:  "(Sources i S) = (DSources i S) \<union> (\<Union> Z \<in> (DSources i S). (Sources i Z))"
     by (rule SourcesDef)
  from assms have "(\<Union> Z \<in> (DSources i S). (Sources i Z)) = Sources i C"
     by auto
  with sDef assms show ?thesis by simp
qed

lemma Sources_2DSources:
  assumes "DSources i S = {C1, C2}" 
  shows    "Sources i S = {C1, C2} \<union> Sources i C1  \<union> Sources i C2"
proof - 
  have sDef:  "(Sources i S) = (DSources i S) \<union> (\<Union> Z \<in> (DSources i S). (Sources i Z))"
     by (rule SourcesDef)
  from assms have "(\<Union> Z \<in> (DSources i S). (Sources i Z)) = Sources i C1  \<union> Sources i C2"
     by auto
  with sDef and assms show ?thesis by simp
qed

lemma Sources_3DSources:
  assumes "DSources i S = {C1, C2, C3}" 
  shows    "Sources i S = {C1, C2, C3} \<union> Sources i C1  \<union> Sources i C2  \<union> Sources i C3"
proof - 
  have sDef: "(Sources i S) = (DSources i S) \<union> (\<Union> Z \<in> (DSources i S). (Sources i Z))" 
     by (rule SourcesDef)
  from assms have "(\<Union> Z \<in> (DSources i S). (Sources i Z)) = Sources i C1  \<union> Sources i C2  \<union> Sources i C3"
     by auto
  with sDef and assms show ?thesis by simp
qed

lemma singleDSourceEmpty4isNotDSource:
  assumes "DAcc i C = {S}" 
         and "Z \<noteq> S"
  shows "C \<notin> (DSources i Z)" 
proof -
  from assms have "(Z \<notin> DAcc i C)"  by simp
  thus ?thesis by (simp add: DAcc_DSourcesNOT)
qed

lemma singleDSourceEmpty4isNotDSourceLevel:
  assumes "DAcc i C = {S}"
  shows "\<forall> Z \<in> (AbstrLevel i). Z \<noteq> S \<longrightarrow> C \<notin> (DSources i Z)" 
using assms  by (metis singleDSourceEmpty4isNotDSource)


lemma "isNotDSource_EmptyDAcc":
  assumes "isNotDSource i S" 
  shows    "DAcc i S ={}"
using assms  by (simp add: DAcc_def isNotDSource_def, auto)

lemma "isNotDSource_EmptyAcc":
  assumes "isNotDSource i S" 
  shows    "Acc i S = {}"
proof -
  have "(Acc i S) = (DAcc i S) \<union> (\<Union> X \<in> (DAcc i S). (Acc i X))"  
     by (rule AccDef)
  thus ?thesis by (metis SUP_empty Un_absorb assms isNotDSource_EmptyDAcc) 
qed

lemma singleDSourceEmpty_Acc:
  assumes "DAcc i C = {S}" 
         and "isNotDSource i S" 
  shows  "Acc i C = {S}"  
proof - 
  have AccC:"(Acc i C) = (DAcc i C) \<union> (\<Union> S \<in> (DAcc i C). (Acc i S))"  
     by (rule AccDef)
  from assms have "Acc i S = {}" by (simp add: isNotDSource_EmptyAcc)
  with AccC show ?thesis
     by (metis SUP_empty UN_insert Un_commute Un_empty_left assms(1)) 
qed

lemma singleDSourceEmpty4isNotSource:
  assumes "DAcc i C = {S}"
         and nSourcS:"isNotDSource i S"
         and "Z \<noteq> S"
  shows "C \<notin> (Sources i Z)" 
proof - 
  from assms have  "Acc i C = {S}"  by (simp add: singleDSourceEmpty_Acc)
  with assms have "Z \<notin> Acc i C" by simp
  thus ?thesis by (simp add: Acc_SourcesNOT)
qed

lemma singleDSourceEmpty4isNotSourceLevel:
  assumes "DAcc i C = {S}"
         and nSourcS:"isNotDSource i S" 
  shows "\<forall> Z \<in> (AbstrLevel i). Z \<noteq> S \<longrightarrow> C \<notin> (Sources i Z)" 
using assms
by (metis singleDSourceEmpty4isNotSource)


lemma singleDSourceLoop:
  assumes "DAcc i C = {S}"
         and "DAcc i S = {C}"
  shows "\<forall> Z \<in> (AbstrLevel i). (Z \<noteq> S \<and> Z \<noteq> C \<longrightarrow> C \<notin> (Sources i Z))" 
using assms
by (metis AccSigleLoop Acc_SourcesNOT empty_iff insert_iff)


(*<*)
(*>*)
subsection \<open>Components that are elementary wrt. data dependencies\<close>

\<comment> \<open>two output channels of a component C are corelated, if they mutually depend on the same local variable(s)\<close>
definition
   outPairCorelated :: "CSet \<Rightarrow> chanID \<Rightarrow> chanID \<Rightarrow> bool"
where
  "outPairCorelated C x y \<equiv>
  (x \<in> OUT C) \<and>   (y \<in> OUT C) \<and> 
  (OUTfromV x) \<inter> (OUTfromV y) \<noteq> {}"

\<comment> \<open>We call a set of output channels of a conponent correlated to it output channel x,\<close>
\<comment> \<open>if they mutually depend on the same local variable(s)\<close>
definition
   outSetCorelated :: "chanID \<Rightarrow> chanID set"
where
  "outSetCorelated x  \<equiv> 
  { y::chanID . \<exists> v::varID. (v \<in> (OUTfromV x) \<and> (y \<in> VARto v)) }"

\<comment> \<open>Elementary component according to the data dependencies.\<close>
\<comment> \<open>This constraint should hold for all components on the abstraction level 1\<close>
definition
elementaryCompDD :: "CSet \<Rightarrow> bool"
where
  "elementaryCompDD C \<equiv> 
  ((\<exists> x. (OUT C) = {x} ) \<or> 
   (\<forall> x \<in> (OUT C). \<forall> y \<in> (OUT C). ((outSetCorelated x) \<inter> (outSetCorelated y) \<noteq> {}) ))"

\<comment> \<open>the set (outSetCorelated x) is empty if x does not depend from any variable\<close>
lemma outSetCorelatedEmpty1:
 assumes "OUTfromV x = {}"
 shows "outSetCorelated x = {}"
using assms by (simp add: outSetCorelated_def)

\<comment> \<open>if x depends from at least one variable and the predicates OUTfromV and VARto are defined correctly,\<close>
\<comment> \<open>the set (outSetCorelated x) contains x itself\<close>
lemma outSetCorelatedNonemptyX:
 assumes "OUTfromV x  \<noteq> {}" and correct3:"OUTfromV_VARto"
 shows "x \<in> outSetCorelated x"
proof -
  from assms have "\<exists> v::varID. x \<in> (VARto v)" 
    by (rule OUTfromV_VARto_lemma)
  from this and assms show ?thesis
    by (simp add:  outSetCorelated_def OUTfromV_VARto_def)
qed

\<comment> \<open>if the set (outSetCorelated x) is empty, this means that x does not depend from any variable\<close>
lemma outSetCorelatedEmpty2:
 assumes "outSetCorelated x = {}"   and correct3:"OUTfromV_VARto"
 shows  "OUTfromV x = {}"
proof (rule ccontr)
  assume OUTfromVNonempty:"OUTfromV x \<noteq> {}"
  from this and correct3 have "x \<in> outSetCorelated x" 
    by (rule outSetCorelatedNonemptyX)
  from this and assms show False by simp
qed

(*<*)
(*>*)
subsection \<open>Set of components needed to check a specific property\<close>

\<comment> \<open>set of components specified on abstreaction level i, which input channels belong to the set chSet\<close>
definition
  inSetOfComponents :: "AbstrLevelsID \<Rightarrow> chanID set \<Rightarrow> CSet set"
where
 "inSetOfComponents i chSet \<equiv>
  {X. (((IN X) \<inter> chSet \<noteq> {})  \<and> X \<in> (AbstrLevel i))}"

\<comment> \<open>Set of components from the abstraction level i, which output channels belong to the set chSet\<close>
definition
  outSetOfComponents :: "AbstrLevelsID \<Rightarrow> chanID set \<Rightarrow> CSet set"
where
 "outSetOfComponents i chSet \<equiv>
  {Y. (((OUT Y) \<inter> chSet \<noteq> {}) \<and> Y \<in> (AbstrLevel i))}"

\<comment> \<open>Set of components from the abstraction level i,\<close>
\<comment> \<open>which have output channels from the set chSet or are sources for such components\<close>
definition
  minSetOfComponents ::  "AbstrLevelsID \<Rightarrow> chanID set \<Rightarrow> CSet set"
where
 "minSetOfComponents i chSet \<equiv>
  (outSetOfComponents i chSet) \<union>
  (\<Union> S \<in> (outSetOfComponents i chSet). (Sources i S))"

\<comment> \<open>Please note that a system output cannot beat the same time a local chanel.\<close>

\<comment> \<open>channel x is a system input on an abstraction level i\<close>
definition systemIN ::"chanID \<Rightarrow> AbstrLevelsID \<Rightarrow> bool"
where
  "systemIN x i \<equiv> (\<exists> C1 \<in> (AbstrLevel i). x \<in> (IN C1)) \<and> (\<forall> C2 \<in> (AbstrLevel i). x \<notin> (OUT C2))"

\<comment> \<open>channel x is a system input on an abstraction level i\<close>
definition systemOUT ::"chanID \<Rightarrow> AbstrLevelsID \<Rightarrow> bool"
where
  "systemOUT x i \<equiv> (\<forall> C1 \<in> (AbstrLevel i). x \<notin> (IN C1)) \<and> (\<exists> C2 \<in> (AbstrLevel i). x \<in> (OUT C2))"

\<comment> \<open>channel x is a system local channel on an abstraction level i\<close>
definition systemLOC ::"chanID \<Rightarrow> AbstrLevelsID \<Rightarrow> bool"
where
  "systemLOC x i \<equiv> (\<exists> C1 \<in> (AbstrLevel i). x \<in> (IN C1)) \<and> (\<exists> C2 \<in> (AbstrLevel i). x \<in> (OUT C2))"

lemma systemIN_noOUT:
  assumes "systemIN x i"
  shows    "\<not> systemOUT x i"
using assms by (simp add: systemIN_def systemOUT_def)

lemma systemOUT_noIN:
  assumes "systemOUT x i"
  shows    "\<not> systemIN x i"
using assms by (simp add: systemIN_def systemOUT_def)

lemma systemIN_noLOC:
  assumes "systemIN x i"
  shows    "\<not> systemLOC x i"
using assms by (simp add: systemIN_def systemLOC_def)

lemma systemLOC_noIN:
  assumes "systemLOC x i"
  shows    "\<not> systemIN x i"
using assms by (simp add: systemIN_def systemLOC_def)

lemma systemOUT_noLOC:
  assumes "systemOUT x i"
  shows    "\<not> systemLOC x i"
using assms by (simp add: systemOUT_def systemLOC_def)

lemma systemLOC_noOUT:
  assumes "systemLOC x i"
  shows    "\<not> systemOUT x i"
using assms by (simp add: systemLOC_def systemOUT_def)

definition
  noIrrelevantChannels ::  "AbstrLevelsID \<Rightarrow> chanID set \<Rightarrow> bool"
where
 "noIrrelevantChannels i chSet \<equiv>
  \<forall> x \<in> chSet. ((systemIN x i) \<longrightarrow>
   (\<exists> Z \<in> (minSetOfComponents i chSet). x \<in> (IN Z)))"


definition
  allNeededINChannels ::  "AbstrLevelsID \<Rightarrow> chanID set \<Rightarrow> bool"
where
 "allNeededINChannels i chSet \<equiv>
  (\<forall> Z \<in> (minSetOfComponents i chSet). \<exists> x \<in> (IN Z). ((systemIN x i) \<longrightarrow> (x \<in> chSet)))"

\<comment> \<open>the set (outSetOfComponents i chSet) should be a subset of all components specified on the abstraction level i\<close>
lemma outSetOfComponentsLimit:
"outSetOfComponents i chSet \<subseteq> AbstrLevel i"
by (metis (lifting) mem_Collect_eq outSetOfComponents_def subsetI)

\<comment> \<open>the set (inSetOfComponents i chSet) should be a subset of all components specified on the abstraction level i\<close>
lemma inSetOfComponentsLimit:
"inSetOfComponents i chSet \<subseteq> AbstrLevel i"
by (metis (lifting) inSetOfComponents_def mem_Collect_eq subsetI)

\<comment> \<open>the set of components, which are sources for the components\<close>
\<comment> \<open>out of (inSetOfComponents i chSet), should be a subset of\<close> 
\<comment> \<open>all components specified on the abstraction level i\<close>
lemma SourcesLevelLimit:
"(\<Union> S \<in> (outSetOfComponents i chSet). (Sources i S)) \<subseteq> AbstrLevel i"
proof -
  have sg1:"outSetOfComponents i chSet \<subseteq> AbstrLevel i"
    by (simp add: outSetOfComponentsLimit)
  have "\<forall> S. S \<in> (outSetOfComponents i chSet) \<longrightarrow> Sources i S \<subseteq> AbstrLevel i"
    by (metis SourcesLevelX)
  from this and sg1 show ?thesis by auto
qed

lemma minSetOfComponentsLimit:
"minSetOfComponents i chSet \<subseteq> AbstrLevel i"
proof -
  have sg1: "outSetOfComponents i chSet \<subseteq> AbstrLevel i"
    by (simp add: outSetOfComponentsLimit)
  have "(\<Union> S \<in> (outSetOfComponents i chSet). (Sources i S)) \<subseteq> AbstrLevel i"
    by (simp add:  SourcesLevelLimit)
  with sg1 show ?thesis  by (simp add: minSetOfComponents_def)
qed 

(*<*)
(*>*)
subsection \<open>Additional properties: Remote Computation\<close>

\<comment> \<open>The value of  $UplSizeHighLoad$ $x$ is True if its $UplSize$ measure is greather that a predifined value\<close>
definition UplSizeHighLoadCh ::  "chanID \<Rightarrow> bool"
where
   "UplSizeHighLoadCh x \<equiv> (x \<in> UplSizeHighLoad)"

\<comment> \<open>if the $Perf$ measure of at least one subcomponent is greather than a predifined value,\<close>
\<comment> \<open>the $Perf$ measure of this component is greather than $HighPerf$ too\<close>
axiomatization HighPerfComp ::  "CSet \<Rightarrow> bool"
where
HighPerfComDef:
   "HighPerfComp C =
   ((C \<in> HighPerfSet) \<or> (\<exists> Z \<in> subcomp C. (HighPerfComp Z)))"

end
