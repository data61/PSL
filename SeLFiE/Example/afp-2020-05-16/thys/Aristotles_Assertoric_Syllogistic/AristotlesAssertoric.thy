(*
Title: Aristotle's Assertoric Syllogistic
Author: Angeliki Koutsoukou-Argyraki, University of Cambridge.
October 2019

We formalise with Isabelle/HOL some basic elements of Aristotle's assertoric syllogistic following
the article from the Stanford Encyclopedia of Philosophy by Robin Smith:
https://plato.stanford.edu/entries/aristotle-logic/.
To this end, we use a set theoretic formulation (covering both individual and general predication).
In particular, we formalise the deductions in the Figures and after that we present Aristotle's
metatheoretical observation that all deductions in the Figures can in fact be reduced to either
Barbara or Celarent. As the formal proofs prove to be straightforward, the interest of this entry 
lies in illustrating the functionality of Isabelle and high efficiency of Sledgehammer for simple 
exercises in philosophy.*)


section\<open>Aristotle's Assertoric Syllogistic\<close>

theory AristotlesAssertoric 
  imports Main 
begin


subsection\<open>Aristotelean Categorical Sentences\<close>

text\<open> Aristotle's universal, particular and indefinite predications (affirmations and denials)
are expressed here using a set theoretic formulation.
Aristotle handles in the same way individual and general predications i.e. 
he gives the same logical analysis to "Socrates is an animal" and "humans are animals".
Here we define the general predication i.e. predications are defined as relations between sets.
This has the benefit that individual predication can also be expressed as set membership (e.g. see
the lemma SocratesMortal). \<close>

definition universal_affirmation :: "'a set  \<Rightarrow>'a set  \<Rightarrow> bool"  (infixr "Q" 80)
  where "A Q B \<equiv> \<forall> b \<in> B . b \<in> A " 

definition universal_denial ::  "'a set  \<Rightarrow>'a set   \<Rightarrow> bool"  (infixr "E" 80)
  where "A E B \<equiv> \<forall> b \<in> B. ( b \<notin> A)  "

definition particular_affirmation ::  " 'a set  \<Rightarrow>'a set  \<Rightarrow> bool"  (infixr "I" 80)
  where "A I B \<equiv> \<exists> b \<in> B. ( b \<in> A) "

definition particular_denial ::  "'a set  \<Rightarrow>'a set \<Rightarrow> bool"  (infixr "Z" 80)
  where "A Z B \<equiv> \<exists> b \<in> B. ( b \<notin> A) "

text\<open> The above four definitions are known as the "square of opposition".\<close>

definition indefinite_affirmation ::  " 'a set \<Rightarrow>'a set \<Rightarrow> bool"  (infixr "QI" 80)
  where "A QI B \<equiv>(( \<forall> b \<in> B. (b \<in> A)) \<or>  (\<exists> b \<in> B. (b \<in> A))) "

definition indefinite_denial ::  "'a set  \<Rightarrow>'a set \<Rightarrow> bool"  (infixr "EZ" 80)
  where "A EZ  B \<equiv> (( \<forall> b \<in> B. (b \<notin> A)) \<or> (\<exists> b \<in> B. (b \<notin> A)))  "

lemma aristo_conversion1 : 
  assumes "A E B" shows "B E A"
  using assms universal_denial_def by blast

lemma aristo_conversion2 : 
  assumes "A I B" shows "B I A"
  using assms unfolding  particular_affirmation_def
  by blast

lemma aristo_conversion3 : assumes "A Q B" and "B \<noteq>{} "  shows "B I A"
  using assms 
  unfolding universal_affirmation_def particular_affirmation_def by blast

text\<open>Remark: Aristotle in general supposes that sets have to be nonempty. Indeed, we observe that 
 in many instances it is necessary to assume that the sets are nonempty,
 otherwise Isabelle's automation finds counterexamples.\<close>

subsection\<open>The Deductions in the Figures ("Moods")\<close>

text\<open>The medieval mnemonic names are used.\<close> 

subsubsection\<open>First Figure\<close>

lemma Barbara:
  assumes "A Q B " and "B Q C" shows "A Q C"
by (meson assms universal_affirmation_def)

lemma Celarent:
  assumes "A E B " and "B Q C" shows "A E C"
by (meson assms universal_affirmation_def universal_denial_def)

lemma Darii:
  assumes  "A Q B" and "B I C" shows "A I C"
by (meson assms particular_affirmation_def universal_affirmation_def)

lemma Ferio:
  assumes  "A E B" and "B I C" shows "A Z C"
by (meson assms particular_affirmation_def particular_denial_def universal_denial_def)

subsubsection\<open>Second Figure\<close>

lemma Cesare:
  assumes  "A E B " and "A Q C" shows "B E C"
using Celarent aristo_conversion1 assms by blast

lemma Camestres:
  assumes  "A Q B " and "A E C" shows "B E C "
using Cesare aristo_conversion1 assms by blast

lemma Festino:
  assumes  "A E B " and "A I C" shows "B Z C "
using Ferio aristo_conversion1 assms by blast

lemma Baroco:
  assumes  "A Q B " and "A Z C" shows "B Z C   "
by (meson assms particular_denial_def universal_affirmation_def)


subsubsection\<open>Third Figure\<close>

lemma Darapti:
  assumes  "A Q C " and "B Q C" and "C \<noteq>{}"   shows "A I B "
  using Darii assms unfolding  universal_affirmation_def particular_affirmation_def
  by blast

lemma Felapton:
  assumes  "A E C" and "B Q C"  and  "C \<noteq>{}"   shows "A Z B"
 using Festino aristo_conversion1 aristo_conversion3 assms by blast

lemma Disamis:
  assumes  "A I C" and "B Q C" shows "A I B"
  using Darii aristo_conversion2 assms by blast

lemma Datisi:
  assumes  "A Q C" and "B I C" shows "A I B"
  using Disamis aristo_conversion2 assms by blast

lemma Bocardo:
  assumes  "A Z C" and "B Q C" shows "A Z B"
 by (meson assms particular_denial_def universal_affirmation_def)

lemma Ferison:  
  assumes  "A E C " and "B I C" shows "A Z B   "
using Ferio aristo_conversion2 assms by blast

subsubsection\<open>Examples\<close>

text\<open>Example of a deduction with general predication.\<close>

lemma GreekMortal : 
  assumes  "Mortal Q Human" and "Human Q Greek "
  shows " Mortal Q Greek "
using assms Barbara by auto

text\<open>Example of a deduction with individual predication.\<close>

lemma SocratesMortal:
  assumes "Socrates \<in> Human " and "Mortal Q Human"  
  shows "Socrates \<in> Mortal " 
using assms by (simp add: universal_affirmation_def)

subsection\<open>Metatheoretical comments\<close>

text\<open>The following are presented to demonstrate one of Aristotle's metatheoretical
explorations. Namely, Aristotle's metatheorem that:
"All deductions in all three Figures can eventually be reduced to either Barbara or Celarent"
is demonstrated by the proofs below and by considering the proofs from the previous subsection. \<close>

lemma Darii_reducedto_Camestres:  
  assumes "A Q B " and "B I C" and "A E C  " (*assms, concl. of Darii  and A E C *)
  shows "A I C"
proof-
  have "B E C" using Camestres \<open> A Q B   \<close>  \<open>A E C\<close>    by blast
  show ?thesis using \<open> B I C \<close>   \<open>B E C\<close> 
    by (simp add: particular_affirmation_def universal_denial_def)
qed

text\<open>It is already evident from the proofs in the previous subsection that:

Camestres can be reduced to Cesare.

Cesare can be reduced to Celarent.

Festino can be reduced to Ferio.\<close>

lemma Ferio_reducedto_Cesare:  assumes
  "A E B " and "B I C" and "A Q C  " (*assms, concl. of Ferio  and A Q C *)
shows "A Z C"
 proof-
  have "B E C" using Cesare \<open>A E B \<close>  \<open>A Q C\<close>  by blast
  show ?thesis using  \<open>B I C \<close>  \<open>B E C\<close>
    by (simp add: particular_affirmation_def universal_denial_def)
qed

lemma Baroco_reducedto_Barbara :
  assumes "A Q B " and " A Z C  " and " B Q C " 
  shows "B Z C" (*assms , concl. of Baroco and  B Q C *)
proof-
  have "A Q C" using  \<open>A Q B \<close>  \<open> B Q C \<close> Barbara by blast
  show ?thesis using  \<open>A Q C\<close>  \<open> A Z C \<close>
    by (simp add: particular_denial_def universal_affirmation_def)
qed

lemma Bocardo_reducedto_Barbara :
  assumes " A Z C" and "B Q C" and "A Q B" 
  shows "A Z B" (*assms, concl of Bocardo and A Q B *)
proof-
  have "A Q C" using  \<open>B Q C\<close>  \<open> A Q B\<close> using Barbara by blast
  show ?thesis using  \<open>A Q C\<close> \<open> A Z C\<close> 
    by (simp add: particular_denial_def universal_affirmation_def)
qed

text\<open>Finally, it is already evident from the proofs in the previous subsection that :

 Darapti can be reduced to Darii.

 Felapton can be reduced to Festino. 

 Disamis can be reduced to Darii. 

 Datisi can be reduced to Disamis. 

 Ferison can be reduced to Ferio. \<close>

text\<open>In conclusion, the aforementioned deductions have thus been shown to be reduced to either 
Barbara or Celarent as follows:

Baroco  $\Rightarrow$ Barbara 

Bocardo $\Rightarrow$ Barbara 

Felapton $\Rightarrow$ Festino $\Rightarrow$ Ferio $\Rightarrow$ Cesare $\Rightarrow$ Celarent 

Datisi $\Rightarrow$ Disamis $\Rightarrow$ Darii $\Rightarrow$ Camestres $\Rightarrow$ Cesare 

Darapti $\Rightarrow$ Darii 

Ferison $\Rightarrow$ Ferio 
\<close>

subsection\<open>Acknowledgements\<close>
 
text\<open>A.K.-A. was supported by the ERC Advanced Grant ALEXANDRIA (Project 742178)
 funded by the European Research Council and led by Professor Lawrence Paulson
 at the University of Cambridge, UK. Thanks to Wenda Li.\<close>

subsection\<open>Bibliography\<close>
text\<open>Smith, Robin, "Aristotle’s Logic", 
The Stanford Encyclopedia of Philosophy (Summer 2019 Edition),
Edward N. Zalta (ed.), URL = @{url "https://plato.stanford.edu/archives/sum2019/entries/aristotle-logic/"}
\<close>

end

