(*  Title:      HMLSL.thy
    Author:     Sven Linker

Definition of HMLSL syntax over traffic snapshots and views for cars
with any sensors. Each formula is a function with a traffic snapshot 
and view as parameters, and evaluates to True or False.
*)

section\<open>Basic HMLSL\<close>
text\<open>
In this section, we define the basic formulas of HMLSL. 
All of these basic formulas and theorems are independent 
of the choice of sensor function. However, they show how
the general operators (chop, changes in perspective, 
atomic formulas) work. 
\<close>

theory HMLSL
  imports "Restriction" "Move" Length
begin

subsection\<open>Syntax of Basic HMLSL\<close>

text \<open>
Formulas are functions associating a traffic snapshot
and a view with a Boolean value.
\<close>
type_synonym \<sigma> = " traffic \<Rightarrow> view \<Rightarrow> bool"

locale hmlsl = restriction+
  fixes sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real" 
  assumes sensors_ge:"(sensors e ts c) > 0"  begin
end

sublocale hmlsl<sensors 
  by (simp add: sensors.intro sensors_ge)

context hmlsl
begin

text\<open>
All formulas are defined as abbreviations. As a consequence,
proofs will directly refer to the semantics of HMLSL, i.e.,
traffic snapshots and views.
\<close>

text\<open>
The first-order operators are direct translations into HOL operators.
\<close>

abbreviation mtrue  :: "\<sigma>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda> ts w. True" 
abbreviation mfalse :: "\<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda> ts w. False"   
abbreviation mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda> ts w. \<not>\<phi>(ts)(w)" 
abbreviation mnegpred :: "(cars\<Rightarrow>\<sigma>)\<Rightarrow>(cars\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda> ts w. \<not>\<Phi>(x)(ts)(w)"   
abbreviation mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<and>\<psi>(ts)(w)"   
abbreviation mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infix "\<^bold>\<or>"50 )
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<or>\<psi>(ts)(w)"   
abbreviation mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longrightarrow>\<psi>(ts)(w)"  
abbreviation mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longleftrightarrow>\<psi>(ts)(w)"  
abbreviation mforall   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")      
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda> ts w.\<forall>x. \<Phi>(x)(ts)(w)"
abbreviation mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
abbreviation mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda> ts w.\<exists>x. \<Phi>(x)(ts)(w)"
abbreviation mexistsB  :: "(('a)\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
abbreviation meq    :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr"\<^bold>="60) \<comment> \<open>Equality\<close>  
  where "x\<^bold>=y \<equiv> \<lambda> ts w. x = y"
abbreviation mgeq :: "('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>\<ge>" 60)
  where "x \<^bold>\<ge> y \<equiv> \<lambda> ts w. x \<ge> y" 
abbreviation mge ::"('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>>" 60)
  where "x \<^bold>> y \<equiv> \<lambda> ts w. x > y"

text\<open>
For the spatial modalities, we use the chopping operations
defined on views. Observe that our chop modalities are existential.
\<close>

abbreviation hchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<frown>" 53)
  where "\<phi> \<^bold>\<frown> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v\<parallel>u) \<and> \<phi>(ts)(v)\<and>\<psi>(ts)(u)"
abbreviation vchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<smile>" 53)
  where "\<phi> \<^bold>\<smile> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v--u) \<and> \<phi>(ts)(v) \<and> \<psi>(ts)(u)"
abbreviation somewhere ::"\<sigma>\<Rightarrow>\<sigma>" ( "\<^bold>\<langle>_\<^bold>\<rangle> " 55)
  where "\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<equiv> \<^bold>\<top> \<^bold>\<frown> (\<^bold>\<top>\<^bold>\<smile>\<phi> \<^bold>\<smile>\<^bold>\<top>)\<^bold>\<frown>\<^bold>\<top>"
abbreviation everywhere::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>]" 55)
  where "\<^bold>[\<phi>\<^bold>] \<equiv> \<^bold>\<not>\<^bold>\<langle>\<^bold>\<not>\<phi>\<^bold>\<rangle>"

text\<open>
To change the perspective of a view, we use 
an operator in the fashion of Hybrid Logic.
\<close>
abbreviation at :: "cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma> " ("\<^bold>@ _ _" 56)
  where "\<^bold>@c \<phi> \<equiv> \<lambda>ts w .  \<forall>v'. (w=c>v') \<longrightarrow> \<phi>(ts)(v')"

text\<open>
The behavioural modalities are defined as usual modal
box-like modalities, where the accessibility relations
are given by the different types of transitions between
traffic snapshots.
\<close>

abbreviation res_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>r'(_') _" 55)
  where "\<^bold>\<box>r(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)" 
abbreviation clm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>c'(_') _" 55)
  where "\<^bold>\<box>c(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation wdres_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdr'(_') _" 55)
  where "\<^bold>\<box>wdr(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation wdclm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdc'(_') _" 55)
  where "\<^bold>\<box>wdc(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation time_box::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>\<^bold>\<tau> _" 55) 
  where "\<^bold>\<box>\<^bold>\<tau> \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts\<^bold>\<leadsto>ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)" 
abbreviation globally::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>G _" 55)
  where "\<^bold>G \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts \<^bold>\<Rightarrow> ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)"


text\<open>
The spatial atoms to refer to reservations, claims
and free space are direct translations of the original
definitions of MLSL \cite{Hilscher2011} into the Isabelle implementation.
\<close>

abbreviation re:: "cars \<Rightarrow> \<sigma>" ("re'(_')" 70)
  where 
    "re(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and> 
                      restrict v (res ts) c = lan v \<and> |lan v|=1" 

abbreviation cl:: "cars \<Rightarrow> \<sigma>" ("cl'(_')" 70)
  where 
    "cl(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and> 
                      restrict v (clm ts) c = lan v \<and> |lan v| = 1" 

abbreviation free:: "\<sigma>" ("free")
  where 
    "free \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> > 0 \<and> |lan v| = 1 \<and>
                  (\<forall>c.  \<parallel>len v ts c\<parallel> = 0 \<or> 
                    (restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>))"  

text\<open>
Even though we do not need them for the subsequent proofs of safety,
we define ways to measure the number of lanes (width) and the
size of the extension (length) of a view. This allows us 
to connect the atomic formulas for reservations and claims
with the atom denoting free space \cite{Linker2015a}.
\<close>

abbreviation width_eq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> = _ " 60)
  where "\<^bold>\<omega> = n \<equiv> \<lambda>  ts v. |lan v| = n"  

abbreviation width_geq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> \<ge> _" 60)
  where "\<^bold>\<omega> \<ge> n \<equiv> \<lambda>  ts v. |lan v| \<ge> n" 

abbreviation width_ge::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> > _" 60)
  where "\<^bold>\<omega> > n \<equiv> (\<^bold>\<omega> = n+1) \<^bold>\<smile> \<^bold>\<top>"

abbreviation length_eq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> = _ " 60)
  where "\<^bold>\<l> = r \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> = r"

abbreviation length_ge:: "real \<Rightarrow> \<sigma>" ("\<^bold>\<l> > _" 60)
  where "\<^bold>\<l> > r \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> > r"

abbreviation length_geq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> \<ge> _" 60)
  where "\<^bold>\<l> \<ge> r \<equiv> (\<^bold>\<l> = r) \<^bold>\<or> (\<^bold>\<l> > r)"

text\<open>
For convenience, we use abbreviations for 
the validity and satisfiability of formulas. While
the former gives a nice way to express theorems, 
the latter is useful within proofs.
\<close>

abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<Turnstile> _" 10 )
  where "\<Turnstile> \<phi> \<equiv>  \<forall>ts. \<forall>v. \<phi>(ts)(v)"

abbreviation satisfies::" traffic \<Rightarrow> view \<Rightarrow> \<sigma> \<Rightarrow> bool" ("_ , _ \<Turnstile> _" 10)
  where "ts,v \<Turnstile> \<phi> \<equiv> \<phi>(ts)(v)"

subsection \<open>Theorems about Basic HMLSL\<close>

lemma hchop_weaken1: " \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<frown> \<^bold>\<top>) " 
  using horizontal_chop_empty_right  by fastforce

lemma hchop_weaken2: " \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<top> \<^bold>\<frown> \<phi>) " 
  using horizontal_chop_empty_left  by fastforce

lemma hchop_weaken: " \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<top> \<^bold>\<frown> \<phi> \<^bold>\<frown> \<^bold>\<top>)" 
  using hchop_weaken1 hchop_weaken2  by metis

lemma hchop_neg1:"\<Turnstile> \<^bold>\<not> (\<phi> \<^bold>\<frown> \<^bold>\<top>) \<^bold>\<rightarrow> ((\<^bold>\<not> \<phi>) \<^bold>\<frown> \<^bold>\<top>)" 
  using horizontal_chop1  by fastforce

lemma hchop_neg2:"\<Turnstile> \<^bold>\<not> (\<^bold>\<top>\<^bold>\<frown>\<phi> ) \<^bold>\<rightarrow> (\<^bold>\<top> \<^bold>\<frown> \<^bold>\<not> \<phi>)"
  using horizontal_chop1  by fastforce

lemma hchop_disj_distr1:"\<Turnstile> ((\<phi> \<^bold>\<frown> (\<psi> \<^bold>\<or> \<chi>)) \<^bold>\<leftrightarrow> ((\<phi> \<^bold>\<frown> \<psi>)\<^bold>\<or>(\<phi> \<^bold>\<frown> \<chi>)))" 
  by blast

lemma hchop_disj_distr2:"\<Turnstile> (((\<psi> \<^bold>\<or> \<chi>)\<^bold>\<frown>\<phi>) \<^bold>\<leftrightarrow> ((\<psi> \<^bold>\<frown> \<phi>)\<^bold>\<or>(\<chi> \<^bold>\<frown> \<phi>)))" 
  by blast

lemma hchop_assoc:"\<Turnstile>\<phi> \<^bold>\<frown> (\<psi> \<^bold>\<frown> \<chi>) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<frown> \<psi>) \<^bold>\<frown> \<chi>"
  using horizontal_chop_assoc1 horizontal_chop_assoc2  by fastforce

lemma v_chop_weaken1:"\<Turnstile> (\<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<smile> \<^bold>\<top>))" 
  using vertical_chop_empty_down  by fastforce

lemma v_chop_weaken2:"\<Turnstile> (\<phi> \<^bold>\<rightarrow> (\<^bold>\<top> \<^bold>\<smile> \<phi>))" 
  using vertical_chop_empty_up  by fastforce

lemma v_chop_assoc:"\<Turnstile>(\<phi> \<^bold>\<smile> (\<psi> \<^bold>\<smile> \<chi>)) \<^bold>\<leftrightarrow> ((\<phi> \<^bold>\<smile> \<psi>) \<^bold>\<smile> \<chi>)"
  using vertical_chop_assoc1 vertical_chop_assoc2  by fastforce

lemma vchop_disj_distr1:"\<Turnstile> ((\<phi> \<^bold>\<smile> (\<psi> \<^bold>\<or> \<chi>)) \<^bold>\<leftrightarrow> ((\<phi> \<^bold>\<smile> \<psi>)\<^bold>\<or>(\<phi> \<^bold>\<smile> \<chi>)))" 
  by blast

lemma vchop_disj_distr2:"\<Turnstile> (((\<psi> \<^bold>\<or> \<chi>) \<^bold>\<smile> \<phi> ) \<^bold>\<leftrightarrow> ((\<psi> \<^bold>\<smile> \<phi>)\<^bold>\<or>(\<chi> \<^bold>\<smile> \<phi>)))" 
  by blast

lemma at_exists :"\<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<exists> c. \<^bold>@c \<phi>)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>\<phi>"
  obtain d where d_def:"d=own v" by blast
  then have "ts,v \<Turnstile> \<^bold>@d \<phi>" using assm switch_refl switch_unique  by fastforce
  thus "ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)" ..
qed

lemma at_conj_distr:"\<Turnstile>(\<^bold>@c ( \<phi> \<^bold>\<and> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>@c \<phi>) \<^bold>\<and> (\<^bold>@c \<psi>))"
  using switch_unique by blast

lemma at_disj_dist:"\<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<or> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>@c \<phi> )  \<^bold>\<or> ( \<^bold>@c \<psi> ))"
  using switch_unique  by fastforce

lemma at_hchop_dist1:"\<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>)) \<^bold>\<rightarrow> ((\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>))" 
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_always_exists  by fastforce
  with assm obtain v1' and v2'
    where chop:"(v'=v1'\<parallel>v2') \<and> (ts,v1' \<Turnstile> \<phi>) \<and> (ts,v2'\<Turnstile>\<psi>)" 
    by blast
  from chop and v' obtain v1 and v2 
    where origin:"(v1=c>v1') \<and> (v2=c>v2') \<and> (v=v1\<parallel>v2)" 
    using switch_hchop2  by fastforce
  hence v1:"ts,v1 \<Turnstile> (\<^bold>@c \<phi>)" and v2:"ts,v2 \<Turnstile> (\<^bold>@c \<psi>)" 
    using switch_unique chop by fastforce+   
  from v1 and v2 and origin show "ts,v \<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)" by blast
qed

lemma at_hchop_dist2:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)) \<^bold>\<rightarrow> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  "
  using switch_unique switch_hchop1 switch_def   by metis

lemma at_hchop_dist:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown>  (\<^bold>@c \<psi>)) \<^bold>\<leftrightarrow> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  "
  using at_hchop_dist1 at_hchop_dist2 by blast

lemma at_vchop_dist1:"\<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>)) \<^bold>\<rightarrow> ( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>))"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_always_exists by fastforce
  with assm obtain v1' and v2' 
    where chop:"(v'=v1'--v2') \<and> (ts,v1' \<Turnstile> \<phi>) \<and> (ts,v2'\<Turnstile>\<psi>)" 
    by blast
  from chop and v' obtain v1 and v2 
    where origin:"(v1=c>v1') \<and> (v2=c>v2') \<and> (v=v1--v2)" 
    using switch_vchop2 by fastforce
  hence v1:"ts,v1 \<Turnstile> (\<^bold>@c \<phi>)" and v2:"ts,v2 \<Turnstile> (\<^bold>@c \<psi>)" 
    using switch_unique chop by fastforce+      
  from v1 and v2 and origin show "ts,v \<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)" by blast
qed

lemma at_vchop_dist2:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) \<^bold>\<rightarrow> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
  using switch_unique switch_vchop1 switch_def   by metis

lemma at_vchop_dist:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) \<^bold>\<leftrightarrow> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
  using at_vchop_dist1 at_vchop_dist2 by blast

lemma at_eq:"\<Turnstile>(\<^bold>@e c \<^bold>= d) \<^bold>\<leftrightarrow> (c \<^bold>= d)"
  using switch_always_exists  by (metis )

lemma at_neg1:"\<Turnstile>(\<^bold>@c \<^bold>\<not> \<phi>) \<^bold>\<rightarrow> \<^bold>\<not> (\<^bold>@c \<phi>)"
  using switch_unique 
  by (metis select_convs switch_def)

lemma at_neg2:"\<Turnstile>\<^bold>\<not> (\<^bold>@c \<phi> ) \<^bold>\<rightarrow> ( (\<^bold>@c \<^bold>\<not> \<phi>))"
  using switch_unique  by fastforce

lemma at_neg :"\<Turnstile>(\<^bold>@c( \<^bold>\<not> \<phi>)) \<^bold>\<leftrightarrow> \<^bold>\<not> (\<^bold>@c \<phi>)"
  using at_neg1 at_neg2 by metis

lemma at_neg':"ts,v \<Turnstile> \<^bold>\<not> (\<^bold>@c \<phi>) \<^bold>\<leftrightarrow> (\<^bold>@c( \<^bold>\<not> \<phi>))" using at_neg by simp

lemma at_neg_neg1:"\<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>)"
  using switch_unique switch_def switch_refl 
  by (metis select_convs switch_def)

lemma at_neg_neg2:"\<Turnstile>\<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>) \<^bold>\<rightarrow> (\<^bold>@c  \<phi>)"
  using switch_unique switch_def switch_refl  
  by metis

lemma at_neg_neg:"\<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>)" 
  using at_neg_neg1 at_neg_neg2 by metis

lemma globally_all_iff:"\<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>c.( \<^bold>G \<phi>))" by simp
lemma globally_all_iff':"ts,v\<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>c.( \<^bold>G \<phi>))" by simp

lemma globally_refl:" \<Turnstile>(\<^bold>G \<phi>) \<^bold>\<rightarrow> \<phi>" 
  using traffic.abstract.refl traffic.move_nothing  by fastforce

lemma globally_4: "\<Turnstile> (\<^bold>G  \<phi>) \<^bold>\<rightarrow> \<^bold>G \<^bold>G \<phi>"
proof (rule allI|rule impI)+
  fix ts v ts' ts'' 
  assume 1:"ts \<^bold>\<Rightarrow> ts'" and 2:"ts' \<^bold>\<Rightarrow> ts''" and 3:"ts,v \<Turnstile> \<^bold>G \<phi>" 
  from 2 and 1 have "ts \<^bold>\<Rightarrow> ts''" using traffic.abs_trans by blast  
  moreover from 1 and 2 have "move ts' ts'' (move ts ts' v) = move ts ts'' v"
    using traffic.move_trans by blast
  with 3 show "ts'', move ts' ts'' (move ts ts' v)  \<Turnstile>\<phi>" using calculation by simp
qed


lemma spatial_weaken: "\<Turnstile> (\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)" 
  using horizontal_chop_empty_left horizontal_chop_empty_right vertical_chop_empty_down
    vertical_chop_empty_up   
  by fastforce

lemma spatial_weaken2:"\<Turnstile> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)"
  using spatial_weaken horizontal_chop_empty_left horizontal_chop_empty_right 
    vertical_chop_empty_down vertical_chop_empty_up 
  by blast 

lemma somewhere_distr: "\<Turnstile> \<^bold>\<langle>\<phi>\<^bold>\<or>\<psi>\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle>\<psi>\<^bold>\<rangle>" 
  by blast

lemma somewhere_and:"\<Turnstile> \<^bold>\<langle>\<phi> \<^bold>\<and> \<psi>\<^bold>\<rangle> \<^bold>\<rightarrow>  \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<langle>\<psi>\<^bold>\<rangle>"
  by blast

lemma somewhere_and_or_distr :"\<Turnstile>(\<^bold>\<langle> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>\<langle> \<chi> \<^bold>\<and>  \<phi> \<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> \<chi> \<^bold>\<and> \<psi> \<^bold>\<rangle>)" 
  by blast

lemma width_add1:"\<Turnstile>((\<^bold>\<omega> = x) \<^bold>\<smile> (\<^bold>\<omega> = y) \<^bold>\<rightarrow> \<^bold>\<omega> = x+y)"
  using vertical_chop_add1  by fastforce

lemma width_add2:"\<Turnstile>((\<^bold>\<omega> = x+y) \<^bold>\<rightarrow>  (\<^bold>\<omega> = x) \<^bold>\<smile> \<^bold>\<omega> = y)"
  using vertical_chop_add2  by fastforce

lemma width_hchop_stable: "\<Turnstile>((\<^bold>\<omega> = x) \<^bold>\<leftrightarrow> ((\<^bold>\<omega> = x) \<^bold>\<frown> (\<^bold>\<omega>=x)))"
  using hchop_def horizontal_chop1 
  by force 

lemma length_geq_zero:"\<Turnstile> (\<^bold>\<l> \<ge> 0)"
  by (metis order.not_eq_order_implies_strict real_int.length_ge_zero)

lemma length_split: "\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<rightarrow> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0))"
  using horizontal_chop_non_empty  by fastforce

lemma length_meld: "\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0) \<^bold>\<rightarrow> (\<^bold>\<l> > 0))"
  using hchop_def real_int.chop_add_length_ge_0 
  by (metis (no_types, lifting))

lemma length_dense:"\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<leftrightarrow> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0))"
  using length_meld length_split by blast

lemma length_add1:"\<Turnstile>((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>= y)) \<^bold>\<rightarrow> (\<^bold>\<l>= x+y)"
  using hchop_def real_int.rchop_def real_int.length_def   by fastforce

lemma length_add2:"\<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0) \<^bold>\<rightarrow> ( (\<^bold>\<l>=x+y) \<^bold>\<rightarrow> ((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)))"
  using horizontal_chop_split_add  by fastforce

lemma length_add:"\<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0) \<^bold>\<rightarrow> ( (\<^bold>\<l>=x+y) \<^bold>\<leftrightarrow> ((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)))"
  using length_add1 length_add2 by blast

lemma length_vchop_stable:"\<Turnstile>(\<^bold>\<l> = x) \<^bold>\<leftrightarrow> ((\<^bold>\<l> = x) \<^bold>\<smile> ( \<^bold>\<l> = x))"
  using vchop_def vertical_chop1  by fastforce

lemma res_ge_zero:"\<Turnstile>(re(c) \<^bold>\<rightarrow> \<^bold>\<l>>0)"
  by blast

lemma clm_ge_zero:"\<Turnstile>(cl(c) \<^bold>\<rightarrow> \<^bold>\<l>>0)"
  by blast

lemma free_ge_zero:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<l>>0"
  by blast

lemma width_res:"\<Turnstile>(re(c) \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
  by auto

lemma width_clm:"\<Turnstile>(cl(c) \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
  by simp

lemma width_free:"\<Turnstile>(free \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
  by simp

lemma width_somewhere_res:"\<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<rightarrow> (\<^bold>\<omega> \<ge> 1)"
proof (rule allI|rule impI)+
  fix ts v
  assume "ts,v \<Turnstile>  \<^bold>\<langle>re(c)\<^bold>\<rangle>"
  then show "ts,v \<Turnstile> (\<^bold>\<omega> \<ge> 1)"
    using view.hchop_def view.vertical_chop_width_mon by fastforce  
qed    

lemma clm_disj_res:"\<Turnstile> \<^bold>\<not> \<^bold>\<langle> cl(c) \<^bold>\<and> re(c) \<^bold>\<rangle>" 
proof (rule allI|rule notI)+
  fix ts v
  assume "ts,v \<Turnstile>\<^bold>\<langle>cl(c) \<^bold>\<and> re(c)\<^bold>\<rangle>"
  then obtain v' where "v' \<le> v \<and> (ts,v' \<Turnstile> cl(c) \<^bold>\<and> re(c))" 
    by (meson view.somewhere_leq)
  then show False using disjoint 
    by (metis card_non_empty_geq_one inf.idem restriction.restriction_clm_leq_one
        restriction.restriction_clm_res_disjoint)
qed

lemma width_ge:"\<Turnstile> (\<^bold>\<omega>> 0) \<^bold>\<rightarrow> (\<^bold>\<exists> x. (\<^bold>\<omega> = x) \<^bold>\<and> (x \<^bold>> 0))"
  using  vertical_chop_add1  add_gr_0 zero_less_one  by auto

lemma two_res_width: "\<Turnstile>((re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<omega> = 2)"
  by (metis one_add_one width_add1)


lemma res_at_most_two:"\<Turnstile>\<^bold>\<not> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )"
proof(rule allI| rule notI )+
  fix ts v 
  assume "ts, v \<Turnstile> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )"
  then obtain v' and v1 and v2 and v3  
    where "v = v1--v'" and "v'=v2--v3" 
    and "ts,v1 \<Turnstile>re(c)" and "ts,v2 \<Turnstile>re(c)" and "ts,v3 \<Turnstile>re(c)" 
    by blast
  then show False 
  proof -
    have "|restrict v' (res ts) c| < |restrict v (res ts) c|"
      using \<open>ts,v1 \<Turnstile>re(c)\<close> \<open>v=v1--v'\<close> restriction.restriction_add_res by auto
    then show ?thesis
      by (metis (no_types) \<open>ts,v2 \<Turnstile> re(c)\<close> \<open>ts,v3 \<Turnstile>re(c)\<close> \<open>v'=v2--v3\<close> not_less 
          one_add_one restriction_add_res restriction_res_leq_two)
  qed
qed

lemma res_at_most_two2:"\<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c)\<^bold>\<rangle>"
  using res_at_most_two by blast

lemma res_at_most_somewhere:"\<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> "
proof (rule allI|rule notI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> )"
  obtain vu and v1 and vm and vd 
    where chops:"(v=vu--v1) \<and> (v1 = vm--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>re(c)\<^bold>\<rangle>) 
                 \<and> (ts,vm \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> ) \<and>( ts,vd \<Turnstile> \<^bold>\<langle> re(c)\<^bold>\<rangle>)"
    using assm by blast
  from chops have res_vu:"|restrict vu (res ts) c| \<ge> 1" 
    by (metis restriction_card_somewhere_mon)
  from chops have res_vm:"|restrict vm (res ts) c| \<ge> 1" 
    by (metis restriction_card_somewhere_mon)
  from chops have res_vd:"|restrict vd (res ts) c| \<ge> 1"
    by (metis restriction_card_somewhere_mon)
  from chops have 
    "|restrict v (res ts) c | = 
     |restrict vu (res ts) c|+ |restrict vm (res ts) c| + |restrict vd (res ts) c| "
    using restriction_add_res by force
  with res_vu and res_vd res_vm have "|restrict v (res ts) c | \<ge> 3" 
    by linarith
  with restriction_res_leq_two show False  
    by (metis not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)
qed

lemma res_adj:"\<Turnstile>\<^bold>\<not>  (re(c) \<^bold>\<smile> (\<^bold>\<omega> > 0) \<^bold>\<smile> re(c)) " 
proof (rule allI|rule notI)+
  fix ts v
  assume "ts,v \<Turnstile> (re(c) \<^bold>\<smile> (\<^bold>\<omega> > 0) \<^bold>\<smile> re(c)) " 
  then obtain v1 and v' and v2 and vn  
    where chop:"(v=v1--v') \<and> (v'=vn--v2) \<and> (ts,v1\<Turnstile>re(c)) 
                \<and> (ts,vn \<Turnstile> \<^bold>\<omega> > 0) \<and> (ts,v2\<Turnstile>re(c))"
    by blast
  hence res1:"|restrict v1 (res ts) c| \<ge> 1" by (simp add: le_numeral_extra(4))
  from chop have res2: "|restrict v2 (res ts) c| \<ge> 1" by (simp add: le_numeral_extra(4))
  from res1 and res2 have "|restrict v (res ts) c| \<ge> 2"
    using chop restriction.restriction_add_res by auto  
  then have resv:"|restrict v (res ts) c| = 2"
    using dual_order.antisym restriction.restriction_res_leq_two by blast
  hence res_two_lanes:"|res ts c| =2" using atMostTwoRes restrict_res 
    by (metis (no_types, lifting) nat_int.card_subset_le dual_order.antisym)
  from this obtain p where p_def:"Rep_nat_int (res ts c) = {p, p+1}" 
    using consecutiveRes by force
  have "Abs_nat_int {p,p+1} \<sqsubseteq> lan v"  
    by (metis Rep_nat_int_inverse atMostTwoRes card_seteq finite_atLeastAtMost
        insert_not_empty nat_int.card'.rep_eq nat_int.card_seq less_eq_nat_int.rep_eq
        p_def resv restrict_res restrict_view)
  have vn_not_e:"lan vn \<noteq> \<emptyset>" using chop
    by (metis nat_int.card_empty_zero less_irrefl width_ge)
  hence consec_vn_v2:"nat_int.consec (lan vn) (lan v2)" 
    using nat_int.card_empty_zero chop nat_int.nchop_def one_neq_zero vchop_def
    by auto
  have v'_not_e:"lan v' \<noteq> \<emptyset>" using chop 
    by (metis less_irrefl nat_int.card_empty_zero view.vertical_chop_assoc2 width_ge)
  hence consec_v1_v':"nat_int.consec (lan v1) (lan v')"
    by (metis (no_types, lifting) nat_int.card_empty_zero chop nat_int.nchop_def
        one_neq_zero vchop_def)
  hence consec_v1_vn:"nat_int.consec (lan v1) (lan vn)"
    by (metis (no_types, lifting) chop consec_vn_v2 nat_int.consec_def 
        nat_int.chop_min vchop_def)
  hence lesser_con:"\<forall>n m. (n \<^bold>\<in> (lan v1) \<and> m \<^bold>\<in> (lan v2) \<longrightarrow> n < m)" 
    using consec_v1_vn consec_vn_v2 nat_int.consec_trans_lesser
    by auto
  have p_in_v1:"p \<^bold>\<in> lan v1" 
  proof (rule ccontr)
    assume "\<not> p \<^bold>\<in> lan v1"
    then have "p \<^bold>\<notin> lan v1" by (simp )
    hence "p \<^bold>\<notin> restrict v1 (res ts) c"  using chop  by (simp add: chop )
    then have "p+1 \<^bold>\<in> restrict v1 (res ts) c"  
    proof -
       have "{p, p + 1} \<inter> (Rep_nat_int (res ts c) \<inter> Rep_nat_int (lan v1)) \<noteq> {}"
         by (metis chop Rep_nat_int_inject bot_nat_int.rep_eq consec_v1_v' 
             inf_nat_int.rep_eq nat_int.consec_def p_def restriction.restrict_def)
      then have "p + 1 \<in> Rep_nat_int (lan v1)"
        using \<open>p \<^bold>\<notin> restrict v1 (res ts) c\<close> inf_nat_int.rep_eq not_in.rep_eq
          restriction.restrict_def by force
      then show ?thesis
        using chop el.rep_eq by presburger
    qed
    hence suc_p:"p+1 \<^bold>\<in> lan v1" using chop by (simp add: chop)
    hence "p+1 \<^bold>\<notin> lan v2" using p_def restrict_def using lesser_con nat_int.el.rep_eq
        nat_int.not_in.rep_eq by auto
    then have "p \<^bold>\<in> restrict v2 (res ts) c"
    proof -
      have f1: "minimum (lan v2) \<in> Rep_nat_int (lan v2)"
        using consec_vn_v2 el.rep_eq minimum_in nat_int.consec_def by simp
      have "lan v2 \<sqsubseteq> res ts c"
        by (metis (no_types) chop restriction.restrict_res)
      then have "minimum (lan v2) = p" 
        using \<open>p + 1 \<^bold>\<notin> lan v2\<close> f1 less_eq_nat_int.rep_eq not_in.rep_eq p_def by auto
      then show ?thesis
        using f1 by (metis chop el.rep_eq)
    qed
    hence p:"p \<^bold>\<in> lan v2" using p_def restrict_def 
      using chop by auto
    show False using lesser_con suc_p p by blast
  qed
  hence p_not_in_v2:"p \<^bold>\<notin> lan v2" using p_def restrict_def lesser_con 
      nat_int.el.rep_eq nat_int.not_in.rep_eq
    by auto
  then have "p+1 \<^bold>\<in> restrict v2 (res ts) c"
  proof -
    have f1: "minimum (lan v2) \<^bold>\<in> lan v2"
      using consec_vn_v2 minimum_in nat_int.consec_def by simp
    obtain x where mini:"x = minimum (lan v2)" by blast
    have "x = p + 1"  
      by (metis IntD1 p_not_in_v2  chop el.rep_eq f1 inf_nat_int.rep_eq insertE mini
          not_in.rep_eq p_def restriction.restrict_def singletonD)
    then show ?thesis 
      using chop f1 mini by auto
  qed
  hence suc_p_in_v2:"p+1 \<^bold>\<in> lan v2" using p_def restrict_def using chop by auto
  have "\<forall>n m. (n \<^bold>\<in> (lan v1) \<and> m \<^bold>\<in> (lan vn) \<longrightarrow> n < m)" 
    using consec_v1_vn nat_int.consec_lesser by auto
  with p_in_v1 have ge_p:"\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow> p < m)" 
    by blast
  have "\<forall>n m. (n \<^bold>\<in> (lan vn) \<and> m \<^bold>\<in> (lan v2) \<longrightarrow> n < m)" 
    using consec_vn_v2 nat_int.consec_lesser by auto
  with suc_p_in_v2 have less_suc_p:"\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow>  m< p+1)"
    by blast
  have "\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow>  (m< p+1 \<and> m > p) )" 
    using ge_p less_suc_p by auto
  hence "\<not>(\<exists>m. (m \<^bold>\<in> lan vn))" 
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right linorder_not_less)
  hence "lan vn = \<emptyset>" using nat_int.non_empty_elem_in by auto
  with vn_not_e show False by blast 
qed

lemma clm_sing:"\<Turnstile>\<^bold>\<not>  (cl(c) \<^bold>\<smile> cl(c)) "
  using atMostOneClm  restriction_add_clm vchop_def restriction_clm_leq_one   
  by (metis (no_types, hide_lams) add_eq_self_zero le_add1 le_antisym one_neq_zero)

lemma clm_sing_somewhere:"\<Turnstile>\<^bold>\<not>  \<^bold>\<langle>cl(c) \<^bold>\<smile> cl(c)\<^bold>\<rangle> "
  using clm_sing by blast

lemma clm_sing_not_interrupted:"\<Turnstile> \<^bold>\<not>(cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile> cl(c))"
  using atMostOneClm  restriction_add_clm vchop_def restriction_clm_leq_one clm_sing
  by (metis (no_types, hide_lams) add.commute add_eq_self_zero dual_order.antisym
      le_add1 one_neq_zero)

lemma clm_sing_somewhere2:"\<Turnstile>\<^bold>\<not>  (\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c) \<^bold>\<smile> \<^bold>\<top>) " 
  using clm_sing_not_interrupted vertical_chop_assoc1 
  by meson

lemma clm_sing_somewhere3:"\<Turnstile>\<^bold>\<not>  \<^bold>\<langle>(\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c) \<^bold>\<smile> \<^bold>\<top>)\<^bold>\<rangle> "  
  by (meson clm_sing_not_interrupted view.vertical_chop_assoc1)

lemma clm_at_most_somewhere:"\<Turnstile>\<^bold>\<not> (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)"
proof (rule allI| rule notI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)"
  obtain vu and vd 
    where chops:"(v=vu--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>cl(c)\<^bold>\<rangle>) \<and> ( ts,vd \<Turnstile> \<^bold>\<langle> cl(c)\<^bold>\<rangle>)"
    using assm by blast
  from chops have clm_vu:"|restrict vu (clm ts) c| \<ge> 1"     
    by (metis restriction_card_somewhere_mon)
  from chops have clm_vd:"|restrict vd (clm ts) c| \<ge> 1"     
    by (metis restriction_card_somewhere_mon)
  from chops have clm_add:
    "|restrict v (clm ts) c | = |restrict vu (clm ts) c| + |restrict vd (clm ts) c|"
    using restriction_add_clm      by auto
  with clm_vu and clm_vd have "|restrict v (clm ts) c | \<ge> 2" 
    using add.commute add_eq_self_zero dual_order.antisym le_add1 less_one not_le
      restriction_res_leq_two
    by linarith
  with restriction_clm_leq_one show False     
    by (metis One_nat_def not_less_eq_eq numeral_2_eq_2)
qed




lemma res_decompose: "\<Turnstile>(re(c)  \<^bold>\<rightarrow> re(c) \<^bold>\<frown> re(c))" 
proof (rule allI| rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>re(c)"
  then obtain v1 and v2 
    where 1:"v=v1\<parallel>v2" and 2:"\<parallel>ext v1\<parallel> > 0" and 3:"\<parallel>ext v2\<parallel> > 0" 
    using  view.horizontal_chop_non_empty by blast
  then have 4:"|lan v1| = 1" and 5:"|lan v2| = 1"
    using assm view.hchop_def by auto
  then have 6:"ts,v1 \<Turnstile>re(c)"  
    by (metis 2 1  assm len_view_hchop_left  restriction.restrict_eq_lan_subs
        restriction.restrict_view restriction.restriction_stable1)
  from 5 have 7:"ts,v2 \<Turnstile>re(c)" 
    by (metis "1" "3" "6" assm len_view_hchop_right restriction.restrict_eq_lan_subs
        restriction.restrict_view restriction.restriction_stable)
  from 1 and 6 and 7 show "ts,v \<Turnstile>re(c) \<^bold>\<frown> re(c)" by blast
qed

lemma res_compose: "\<Turnstile>(re(c) \<^bold>\<frown> re(c)  \<^bold>\<rightarrow> re(c))"     
  using  real_int.chop_dense len_compose_hchop hchop_def length_dense restrict_def
  by (metis (no_types, lifting))

lemma res_dense:"\<Turnstile>re(c) \<^bold>\<leftrightarrow> re(c) \<^bold>\<frown> re(c)"
  using res_decompose res_compose by blast

lemma res_continuous :"\<Turnstile>(re(c)) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown> ( \<^bold>\<not>re(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))"     
  by (metis (no_types, lifting) hchop_def len_view_hchop_left len_view_hchop_right
      restrict_def)

lemma no_clm_before_res:"\<Turnstile>\<^bold>\<not>(cl(c) \<^bold>\<frown> re(c))"  
  by (metis (no_types, lifting) nat_int.card_empty_zero nat_int.card_subset_le
      disjoint hchop_def inf_assoc inf_le1 not_one_le_zero restrict_def)

lemma no_clm_before_res2:"\<Turnstile>\<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))"
proof (rule ccontr)
  assume "\<not> (\<Turnstile> \<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c)))"
  then obtain ts and v where assm:"ts,v \<Turnstile> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))" by blast
  then have clm_subs:"restrict v (clm ts) c = restrict v (res ts) c"
    using restriction_stable
    by (metis (no_types, lifting) hchop_def restrict_def)      
  have "restrict v (clm ts )c \<noteq> \<emptyset>" 
    using assm nat_int.card_non_empty_geq_one restriction_stable1
    by auto
  then have res_in_neq:"restrict v (clm ts) c \<sqinter> restrict v (res ts) c \<noteq>\<emptyset>"
    using clm_subs inf_absorb1
    by (simp )   
  then show False using restriction_clm_res_disjoint      
    by (metis inf_commute restriction.restriction_clm_res_disjoint)    
qed

lemma clm_decompose: "\<Turnstile>(cl(c)  \<^bold>\<rightarrow> cl(c) \<^bold>\<frown> cl(c))" 
proof (rule allI|rule impI)+
  fix ts v
  assume assm: "ts,v \<Turnstile> cl(c)"
  have restr:"restrict v (clm ts) c = lan v" using assm by simp
  have len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" using assm by simp
  have len:"len v ts c = ext v" using assm by simp
  obtain v1 v2 where chop:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0 " 
    using assm view.horizontal_chop_non_empty    
    using length_split by blast    
  from chop and len have len_v1:"len v1 ts c = ext v1" 
    using len_view_hchop_left by blast
  from chop and len have len_v2:"len v2 ts c = ext v2" 
    using len_view_hchop_right by blast
  from chop and restr have restr_v1:"restrict v1 (clm ts) c = lan v1"     
    by (metis (no_types, lifting) hchop_def restriction.restriction_stable1)     
  from chop and restr have restr_v2:"restrict v2 (clm ts) c = lan v2"     
    by (metis (no_types, lifting) hchop_def restriction.restriction_stable2) 
  from chop and len_v1 len_v2 restr_v1 restr_v2 show "ts,v \<Turnstile>cl(c) \<^bold>\<frown> cl(c)"
    using hchop_def assm by force
qed


lemma clm_compose: "\<Turnstile>(cl(c) \<^bold>\<frown> cl(c)  \<^bold>\<rightarrow> cl(c))" 
  using  real_int.chop_dense len_compose_hchop hchop_def length_dense restrict_def     
  by (metis (no_types, lifting))

lemma clm_dense:"\<Turnstile>cl(c) \<^bold>\<leftrightarrow> cl(c) \<^bold>\<frown> cl(c)"
  using clm_decompose clm_compose by blast

lemma clm_continuous :"\<Turnstile>(cl(c)) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( \<^bold>\<not>cl(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))"     
  by (metis (no_types, lifting) hchop_def len_view_hchop_left len_view_hchop_right
      restrict_def)


lemma res_not_free: "\<Turnstile>(\<^bold>\<exists> c. re(c) \<^bold>\<rightarrow> \<^bold>\<not>free)" 
  using nat_int.card_empty_zero one_neq_zero by auto

lemma clm_not_free: "\<Turnstile>(\<^bold>\<exists> c. cl(c) \<^bold>\<rightarrow> \<^bold>\<not>free)"
  using nat_int.card_empty_zero by auto

lemma free_no_res:"\<Turnstile>(free \<^bold>\<rightarrow>  \<^bold>\<not>(\<^bold>\<exists> c. re(c)))" 
  using nat_int.card_empty_zero one_neq_zero 
  by (metis less_irrefl)

lemma free_no_clm:"\<Turnstile>(free \<^bold>\<rightarrow>  \<^bold>\<not>(\<^bold>\<exists> c. cl(c)))" 
  using nat_int.card_empty_zero one_neq_zero by (metis less_irrefl)

lemma free_decompose:"\<Turnstile>free \<^bold>\<rightarrow> ( free \<^bold>\<frown> free)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>free"
  obtain v1 and v2 
    where non_empty_v1_v2:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0"
    using assm length_dense by blast
  have one_lane:"|lan v1| = 1 \<and> |lan v2| = 1" 
    using assm hchop_def non_empty_v1_v2
    by auto
  have nothing_on_v1:
    " (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or> (restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))"     
    by (metis (no_types, lifting) assm len_empty_on_subview1 non_empty_v1_v2
        restriction_stable1)
  have nothing_on_v2:
    " (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or> (restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"     
    by (metis (no_types, lifting) assm len_empty_on_subview2 non_empty_v1_v2
        restriction_stable2)
  have  
    "(v=v1\<parallel>v2) 
    \<and> 0 < \<parallel>ext v1\<parallel> \<and> |lan v1| = 1 
    \<and> (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or>( restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))
    \<and> 0 < \<parallel>ext v2\<parallel> \<and> |lan v2| = 1
    \<and> (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or>( restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"
    using non_empty_v1_v2 nothing_on_v1 nothing_on_v2 one_lane by blast      
  then show "ts,v \<Turnstile>(free \<^bold>\<frown> free)" by blast
qed

lemma free_compose:"\<Turnstile>(free \<^bold>\<frown> free) \<^bold>\<rightarrow> free"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>free \<^bold>\<frown> free"
  have len_ge_0:"\<parallel>ext v\<parallel> > 0" 
    using assm length_meld by blast
  have widt_one:"|lan v| = 1" using assm     
    by (metis horizontal_chop_width_stable)
  have no_car:
    "(\<forall>c. \<parallel>len v ts c\<parallel> = 0 \<or> restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>)"  
  proof (rule ccontr)
    assume 
      "\<not>(\<forall>c. \<parallel>len v ts c\<parallel> = 0 
           \<or> (restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>))" 
    then obtain c 
      where ex:
        "\<parallel>len v ts c\<parallel> \<noteq> 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" 
      by blast
    from ex have 1:"\<parallel>len v ts c\<parallel> > 0" 
      using less_eq_real_def real_int.length_ge_zero by auto
    have "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" using ex ..
    then show False
    proof
      assume "restrict v (clm ts) c \<noteq> \<emptyset>"
      then show False 
        by (metis (no_types, hide_lams) assm add.left_neutral ex len_hchop_add
            restriction.restrict_def view.hchop_def)    
    next
      assume "restrict v (res ts) c \<noteq> \<emptyset>"
      then show False 
        by (metis (no_types, hide_lams) assm add.left_neutral ex len_hchop_add 
            restriction.restrict_def view.hchop_def)  
    qed
  qed
  show "ts,v \<Turnstile>free"
    using len_ge_0 widt_one no_car by blast
qed


lemma free_dense:"\<Turnstile>free \<^bold>\<leftrightarrow> (free \<^bold>\<frown> free)"
  using free_decompose free_compose by blast

lemma free_dense2:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<top> \<^bold>\<frown> free \<^bold>\<frown> \<^bold>\<top>"
  using horizontal_chop_empty_left horizontal_chop_empty_right  by fastforce

text \<open>
The next lemmas show the connection between the spatial. In particular,
if the view consists of one lane and a non-zero extension, where neither
a reservation nor a car resides, the view satisfies free (and vice versa). 
\<close>

lemma no_cars_means_free:
  "\<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))) \<^bold>\<rightarrow> free" 
proof (rule allI|rule impI)+
  fix ts v
  assume assm:
    "ts,v \<Turnstile> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
  have ge_0:"ts,v \<Turnstile> \<^bold>\<l> > 0" using assm by best
  have one_lane:"ts,v \<Turnstile>\<^bold>\<omega> = 1" using assm by best    
  show "ts,v \<Turnstile> free"
  proof (rule ccontr)
    have no_car: "ts,v \<Turnstile>\<^bold>\<not>( \<^bold>\<exists> c.  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
      using assm by best
    assume "ts,v \<Turnstile> \<^bold>\<not> free"
    hence contra:
      "\<not>(\<forall>c. \<parallel>len v ts c\<parallel> = 0 \<or> restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>)"
      using ge_0 one_lane by blast
    hence ex_car:
      "\<exists>c. \<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" 
      using real_int.length_ge_zero dual_order.antisym not_le 
      by metis
    obtain c where c_def:
      "\<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)"       
      using ex_car by blast
    hence "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" by best
    thus False 
    proof
      assume "restrict v (clm ts) c \<noteq> \<emptyset>"
      with one_lane have clm_one:"|restrict v (clm ts) c| = 1" 
        using el_in_restriction_clm_singleton      
        by (metis card_non_empty_geq_one dual_order.antisym restriction.restriction_clm_leq_one)
      obtain v1 and v2 and v3 and v4 
        where "v=v1\<parallel>v2" and "v2=v3\<parallel>v4" 
          and len_eq:"len v3 ts c = ext v3 \<and> \<parallel>len v3 ts c\<parallel> = \<parallel>len v ts c\<parallel> " 
        using horizontal_chop_empty_left horizontal_chop_empty_right 
          len_fills_subview c_def by blast
      then have res_non_empty:"restrict v3 (clm ts) c \<noteq> \<emptyset>" 
        using \<open>restrict v (clm ts) c \<noteq> \<emptyset>\<close> restriction_stable restriction_stable1
        by auto
      have len_non_empty:"\<parallel>len v3 ts c\<parallel> > 0" 
        using len_eq c_def by auto
      have "|restrict v3 (clm ts) c| =1 " 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> clm_one restriction_stable restriction_stable1
        by auto
      have v3_one_lane:"|lan v3| = 1" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> hchop_def one_lane
        by auto
      have clm_fills_v3:"restrict v3 (clm ts) c = lan v3" 
      proof (rule ccontr)
        assume  aux:"restrict v3 (clm ts) c \<noteq> lan v3"
        have "restrict v3 (clm ts) c \<sqsubseteq> lan v3"      
          by (simp add: restrict_view)
        hence "\<exists>n. n \<^bold>\<notin> restrict v3 (clm ts) c \<and> n \<^bold>\<in> lan v3" 
          using aux \<open>|restrict v3 (clm ts) c| = 1\<close> 
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        hence "|lan v3| > 1" 
          using \<open>| (restrict v3 (clm ts) c)| = 1\<close> \<open>restrict v3 (clm ts) c \<le> lan v3\<close> aux
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        thus False using v3_one_lane by auto
      qed
      have "\<parallel>ext v3\<parallel> > 0" using c_def len_eq by auto
      have "ts, v3 \<Turnstile> cl(c)" using clm_one len_eq c_def clm_fills_v3 v3_one_lane
        by auto
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> by blast
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" by blast
      thus False using no_car by best
    next
      assume "restrict v (res ts) c \<noteq> \<emptyset>"
      with one_lane have clm_one:"|restrict v (res ts) c| = 1" 
        using el_in_restriction_clm_singleton      
        by (metis nat_int.card_non_empty_geq_one nat_int.card_subset_le 
            dual_order.antisym restrict_view)
      obtain v1 and v2 and v3 and v4 
        where "v=v1\<parallel>v2" and "v2=v3\<parallel>v4" 
          and len_eq:"len v3 ts c = ext v3 \<and> \<parallel>len v3 ts c\<parallel> = \<parallel>len v ts c\<parallel> " 
        using horizontal_chop_empty_left horizontal_chop_empty_right 
          len_fills_subview c_def by blast
      then have res_non_empty:"restrict v3 (res ts) c \<noteq> \<emptyset>" 
        using \<open>restrict v (res ts) c \<noteq> \<emptyset>\<close> restriction_stable restriction_stable1
        by auto
      have len_non_empty:"\<parallel>len v3 ts c\<parallel> > 0" 
        using len_eq c_def by auto
      have "|restrict v3 (res ts) c| =1 " 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> clm_one restriction_stable restriction_stable1
        by auto
      have v3_one_lane:"|lan v3| = 1" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> hchop_def one_lane
        by auto
      have "restrict v3 (res ts) c = lan v3" 
      proof (rule ccontr)
        assume  aux:"restrict v3 (res ts) c \<noteq> lan v3"
        have "restrict v3 (res ts) c \<sqsubseteq> lan v3"      
          by (simp add: restrict_view)
        hence "\<exists>n. n \<^bold>\<notin> restrict v3 (res ts) c \<and> n \<^bold>\<in> lan v3"
          using aux \<open>|restrict v3 (res ts) c| = 1\<close> restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        hence "|lan v3| > 1" 
          using \<open>| (restrict v3 (res ts) c)| = 1\<close> \<open>restrict v3 (res ts) c \<le> lan v3\<close> aux
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        thus False using v3_one_lane by auto
      qed
      have "\<parallel>ext v3\<parallel> > 0" using c_def len_eq by auto
      have "ts, v3 \<Turnstile> re(c)" 
        using clm_one len_eq c_def \<open>restrict v3 (res ts) c = lan v3\<close> v3_one_lane
        by auto
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> by blast
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" by blast
      thus False using no_car by best
    qed
  qed
qed

lemma free_means_no_cars:
  "\<Turnstile>free \<^bold>\<rightarrow> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))" 
proof (rule allI | rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile> free"
  have no_car:"ts,v \<Turnstile>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
  proof (rule ccontr)
    assume "\<not> (ts,v \<Turnstile>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    hence contra:"ts,v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>" by blast
    from this obtain c and v1 and v' and v2 and vc where 
      vc_def:"(v=v1\<parallel>v') \<and> (v'=vc\<parallel>v2) \<and> (ts,vc \<Turnstile> cl(c) \<^bold>\<or> re(c))" by blast
    hence len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" 
      by (metis len_empty_on_subview1 len_empty_on_subview2 less_eq_real_def
          real_int.length_ge_zero)
    from vc_def have vc_ex_car:
      "restrict vc (clm ts) c \<noteq> \<emptyset> \<or> restrict vc (res ts) c \<noteq>\<emptyset>" 
      using nat_int.card_empty_zero one_neq_zero by auto
    have eq_lan:"lan v = lan vc" using vc_def hchop_def by auto
    hence v_ex_car:"restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq>\<emptyset>" 
      using vc_ex_car by (simp add: restrict_def)
    from len_ge_zero and v_ex_car and assm show False by force
  qed
  with assm show 
    "ts,v \<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    by blast
qed

lemma free_eq_no_cars:
  "\<Turnstile>free \<^bold>\<leftrightarrow> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))" 
  using no_cars_means_free free_means_no_cars by blast

lemma free_nowhere_res:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown> (re(c)) \<^bold>\<frown> \<^bold>\<top>)"
  using free_eq_no_cars by blast

lemma two_res_not_res: "\<Turnstile>((re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<not>re(c))" 
  by (metis add_eq_self_zero one_neq_zero width_add1)

lemma two_clm_width: "\<Turnstile>((cl(c) \<^bold>\<smile> cl(c)) \<^bold>\<rightarrow> \<^bold>\<omega> = 2)"
  by (metis one_add_one width_add1)

lemma two_res_no_car: "\<Turnstile>(re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c. ( cl(c) \<^bold>\<or> re(c)) )" 
  by (metis add_eq_self_zero one_neq_zero width_add1)

lemma two_lanes_no_car:"\<Turnstile>(\<^bold>\<not> \<^bold>\<omega>= 1) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c)))"
  by simp

lemma empty_no_car:"\<Turnstile>( \<^bold>\<l> = 0) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c)))"
  by simp

lemma car_one_lane_non_empty: "\<Turnstile>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c))) \<^bold>\<rightarrow> ((\<^bold>\<omega> =1) \<^bold>\<and> (\<^bold>\<l> > 0))"
  by blast

lemma one_lane_notfree:
  "\<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<and> (\<^bold>\<not> free) \<^bold>\<rightarrow> ( (\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> ))"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<and> (\<^bold>\<not> free)"
  hence not_free:"ts,v \<Turnstile>\<^bold>\<not> free" by blast
  with free_eq_no_cars have 
    "ts,v \<Turnstile>\<^bold>\<not> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    by blast
  hence "ts,v \<Turnstile> \<^bold>\<not>  (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))" 
    using assm by blast
  thus "ts,v \<Turnstile>(\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> )" by blast
qed

lemma one_lane_empty_or_car:
  "\<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<rightarrow> (free \<^bold>\<or> (\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> ))"
  using one_lane_notfree by blast
end
end
