section \<open>Application example from IoT healthcare\<close> 
text \<open>The  example of an IoT healthcare systems is taken from the context of the CHIST-ERA project
SUCCESS \cite{suc:16}.  In this system architecture, data is collected by sensors 
in the home or via a smart phone helping to monitor bio markers of the patient. The data 
collection is in a cloud based server to enable hospitals (or scientific institutions) 
to access the data which is controlled via the smart phone.
The identities Patient and Doctor represent patients
and their doctors; double quotes ''s'' indicate strings 
in Isabelle/HOL.
The global policy is `only the patient and the doctor can access the data in the cloud'.\<close>
theory GDPRhealthcare
imports Infrastructure
begin
text \<open>Local policies are represented as a function over an @{text \<open>igraph G\<close>} 
      that additionally assigns each location of a scenario to its local policy 
      given as a pair of requirements to an actor (first element of the pair) in 
      order to grant him actions in the location (second element of the pair). 
      The predicate @{text \<open>@G\<close>} checks whether an actor is at a given location 
       in the @{text \<open>igraph G\<close>}.\<close>
locale scenarioGDPR = 
fixes gdpr_actors :: "identity set"
defines gdpr_actors_def: "gdpr_actors \<equiv> {''Patient'', ''Doctor''}"
fixes gdpr_locations :: "location set"
defines gdpr_locations_def: "gdpr_locations \<equiv> 
          {Location 0, Location 1, Location 2, Location 3}"
fixes sphone :: "location"
defines sphone_def: "sphone \<equiv> Location 0"
fixes home :: "location"
defines home_def: "home \<equiv> Location 1"
fixes hospital :: "location"
defines hospital_def: "hospital \<equiv> Location 2"
fixes cloud :: "location"
defines cloud_def: "cloud \<equiv> Location 3"
fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<noteq> ''Doctor'' 
                 \<longrightarrow> \<not>(enables I hospital (Actor a) eval)"
fixes global_policy' :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I a \<equiv> a \<notin> gdpr_actors 
                 \<longrightarrow> \<not>(enables I cloud (Actor a) get)"  
fixes ex_creds :: "actor \<Rightarrow> (string set * string set)"
defines ex_creds_def: "ex_creds \<equiv> (\<lambda> x. if x = Actor ''Patient'' then 
                         ({''PIN'',''skey''}, {}) else 
                            (if x = Actor ''Doctor'' then
                                ({''PIN''},{}) else ({},{})))"
fixes ex_locs :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locs \<equiv> (\<lambda> x.  if x = cloud then
             (''free'',{((Actor ''Patient'',{Actor ''Doctor''}),42)}) 
             else ('''',{}))"
fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x.  if x = home then {''Patient''}  
                 else (if x = hospital then {''Doctor'', ''Eve''} 
                       else {}))"
(* The nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax)  
fixes ex_loc_ass_alt :: "location \<Rightarrow> identity set"
defines ex_loc_ass_alt_def: "ex_loc_ass_alt \<equiv>
          (\<lambda> x.  (case x of 
             Location (Suc 0) \<Rightarrow> {''Patient''}  
           | Location (Suc (Suc 0)) \<Rightarrow> {''Doctor'', ''Eve''} 
           |  _ \<Rightarrow> {}))"
*)
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
     ex_loc_ass
     ex_creds ex_locs"
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient''} else 
           (if x = hospital then {''Doctor'',''Eve''} else {})) 
     ex_creds ex_locs"
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph 
     {(home, cloud), (sphone, cloud), (cloud,hospital)}
       (\<lambda> x. if x = cloud then {''Patient'', ''Eve''} else 
           (if x = hospital then {''Doctor''} else {})) 
     ex_creds ex_locs"
(* Same as above: the nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax) 
fixes local_policies_alt :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_alt_def: "local_policies_alt G \<equiv> 
    (\<lambda> x. case x of 
         Location (Suc 0) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location 0 \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
       | Location (Suc (Suc (Suc 0))) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location (Suc (Suc 0)) \<Rightarrow>
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
       | _ \<Rightarrow>  {})"
*)
fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = home then
        {(\<lambda> y. True, {put,get,move,eval})}
          else (if x = sphone then 
             {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
                else (if x = cloud then
                {(\<lambda> y. True, {put,get,move,eval})}
                       else (if x = hospital then
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} else {}))))"
(* problems with case in locales?
defines local_policies_def: "local_policies G x \<equiv> 
     (case x of 
       home \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | sphone \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
     | cloud \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | hospital \<Rightarrow> {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
     | _ \<Rightarrow>  {})"
*)
fixes gdpr_scenario :: "infrastructure"
defines gdpr_scenario_def:
"gdpr_scenario \<equiv> Infrastructure ex_graph local_policies"
fixes Igdpr :: "infrastructure set"
defines Igdpr_def:
  "Igdpr \<equiv> {gdpr_scenario}"
(* other states of scenario *)
(* First step: Patient goes onto cloud *)
fixes gdpr_scenario' :: "infrastructure"
defines gdpr_scenario'_def:
"gdpr_scenario' \<equiv> Infrastructure ex_graph' local_policies"
fixes GDPR' :: "infrastructure set"
defines GDPR'_def:
  "GDPR' \<equiv> {gdpr_scenario'}"
(* Second step: Eve goes onto cloud from where she'll be able to get the data *)
fixes gdpr_scenario'' :: "infrastructure"
defines gdpr_scenario''_def:
"gdpr_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"
fixes GDPR'' :: "infrastructure set"
defines GDPR''_def:
  "GDPR'' \<equiv> {gdpr_scenario''}"
fixes gdpr_states
defines gdpr_states_def: "gdpr_states \<equiv> { I. gdpr_scenario \<rightarrow>\<^sub>i* I }"
fixes gdpr_Kripke
defines "gdpr_Kripke \<equiv> Kripke gdpr_states {gdpr_scenario}"
fixes sgdpr 
defines "sgdpr \<equiv> {x. \<not> (global_policy' x ''Eve'')}"  
begin
subsection \<open>Using Attack Tree Calculus\<close>
text \<open>Since we consider a predicate transformer semantics, we use sets of states 
     to represent properties. For example, the attack property is given by the above
     @{text \<open>set sgdpr\<close>}.

The attack we are interested in is to see whether for the scenario

@{text \<open>gdpr scenario \<equiv> Infrastructure ex_graph local_policies\<close>}

from the initial state 

@{text \<open>Igdpr \<equiv>{gdpr scenario}\<close>}, 

the critical state
@{text \<open>sgdpr\<close>} can be reached, i.e., is there a valid attack @{text \<open>(Igdpr,sgdpr)\<close>}?

We first present a number of lemmas showing single and multi-step state transitions
for relevant states reachable from our @{text \<open>gdpr_scenario\<close>}.\<close>
lemma step1: "gdpr_scenario  \<rightarrow>\<^sub>n gdpr_scenario'"
proof (rule_tac l = home and a = "''Patient''" and l' = cloud in move)
  show "graphI gdpr_scenario = graphI gdpr_scenario" by (rule refl)
next show "''Patient'' @\<^bsub>graphI gdpr_scenario\<^esub> home" 
    by (simp add: gdpr_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def)
next show "home \<in> nodes (graphI gdpr_scenario)"
    by (simp add: gdpr_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI gdpr_scenario)"
    by (simp add: gdpr_scenario_def nodes_def ex_graph_def, blast)
next show "''Patient'' \<in> actors_graph (graphI gdpr_scenario)"
    by (simp add: actors_graph_def gdpr_scenario_def ex_graph_def ex_loc_ass_def nodes_def, blast)
next show "enables gdpr_scenario cloud (Actor ''Patient'') move"
    by (simp add: enables_def gdpr_scenario_def ex_graph_def local_policies_def
                    ex_creds_def ex_locs_def has_def credentials_def)
next show "gdpr_scenario' =
    Infrastructure (move_graph_a ''Patient'' home cloud (graphI gdpr_scenario)) (delta gdpr_scenario)"
    apply (simp add: gdpr_scenario'_def ex_graph'_def move_graph_a_def 
                     gdpr_scenario_def ex_graph_def home_def cloud_def hospital_def
                     ex_loc_ass_def ex_creds_def)
    apply (rule ext)
    by (simp add: hospital_def)
qed

lemma step1r: "gdpr_scenario  \<rightarrow>\<^sub>n* gdpr_scenario'"
proof (simp add: state_transition_in_refl_def)
  show " (gdpr_scenario, gdpr_scenario') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "gdpr_scenario'  \<rightarrow>\<^sub>n gdpr_scenario''"
proof (rule_tac l = hospital and a = "''Eve''" and l' = cloud in move, rule refl)
  show "''Eve'' @\<^bsub>graphI gdpr_scenario'\<^esub> hospital"
   by (simp add: gdpr_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def)
next show "hospital \<in> nodes (graphI gdpr_scenario')"
    by (simp add: gdpr_scenario'_def ex_graph'_def hospital_def cloud_def atI_def nodes_def, blast)
next show "cloud \<in> nodes (graphI gdpr_scenario')"
    by (simp add: gdpr_scenario'_def nodes_def ex_graph'_def, blast)
next show "''Eve'' \<in> actors_graph (graphI gdpr_scenario')"
    by (simp add: actors_graph_def gdpr_scenario'_def ex_graph'_def nodes_def
                     hospital_def cloud_def, blast)
next show "enables gdpr_scenario' cloud (Actor ''Eve'') move"
    by (simp add: enables_def gdpr_scenario'_def ex_graph_def local_policies_def
                  ex_creds_def ex_locs_def has_def credentials_def cloud_def sphone_def)
next show "gdpr_scenario'' =
    Infrastructure (move_graph_a ''Eve'' hospital cloud (graphI gdpr_scenario')) (delta gdpr_scenario')"
    apply (simp add: gdpr_scenario'_def ex_graph''_def move_graph_a_def gdpr_scenario''_def 
                     ex_graph'_def home_def cloud_def hospital_def ex_creds_def)
    apply (rule ext)
    apply (simp add: hospital_def)
    by blast
qed

lemma step2r: "gdpr_scenario'  \<rightarrow>\<^sub>n* gdpr_scenario''"
proof (simp add: state_transition_in_refl_def)
  show "(gdpr_scenario', gdpr_scenario'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed
     
(* Attack example: Eve can get onto cloud and get Patient's data 
   because the policy allows Eve to get on cloud.
   This attack can easily be fixed by disabling Eve to "get"
   in the policy (just change the "True" for cloud to a set with no 
   Eve in it).
   However, it would not prevent Insider attacks (where Eve is 
   impersonating the Doctor, for example). Insider attacks can
   be checked using the UasI predicate.
*)
text \<open>For the Kripke structure

@{text \<open>gdpr_Kripke \<equiv> Kripke { I. gdpr_scenario \<rightarrow>\<^sub>i* I } {gdpr_scenario}\<close>}

we first derive a valid and-attack using the attack tree proof calculus.

@{text \<open>"\<turnstile>[\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>\<close>}

The set @{text \<open>GDPR'\<close>} (see above) is an intermediate state where Eve accesses the cloud.\<close>

lemma gdpr_ref: "[\<N>\<^bsub>(Igdpr,sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>)"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>]" and
                  l'' = "[]" and si = Igdpr and si' = Igdpr and 
                  si'' = sgdpr and si''' = sgdpr in refI, simp, rule refl)
  show "([\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>) =
    ([] @ [\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>)"
  by simp
qed

lemma att_gdpr: "\<turnstile>([\<N>\<^bsub>(Igdpr,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Igdpr, GDPR')\<^esub>"
    apply (simp add: Igdpr_def GDPR'_def att_base)
    using state_transition_infra_def step1 by blast
next 
  have "\<not> global_policy' gdpr_scenario'' ''Eve''" "gdpr_scenario' \<rightarrow>\<^sub>n gdpr_scenario''"
      using step2
      by (auto simp: global_policy'_def gdpr_scenario''_def gdpr_actors_def 
                      enables_def local_policies_def cloud_def sphone_def intro!: step2)
  then show "\<turnstile>([\<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(GDPR', sgdpr)\<^esup>)"
    apply (subst att_and)
    apply (simp add: GDPR'_def sgdpr_def att_base)
    using state_transition_infra_def by blast
qed

lemma gdpr_abs_att: "\<turnstile>\<^sub>V([\<N>\<^bsub>(Igdpr,sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr,sgdpr)\<^esup>)"
  by (rule ref_valI, rule gdpr_ref, rule att_gdpr)

text \<open>We can then simply apply the Correctness theorem @{text \<open>AT EF\<close>} to immediately 
      prove the following CTL statement.

      @{text \<open>gdpr_Kripke \<turnstile> EF sgdpr\<close>}

This application of the meta-theorem of Correctness of attack trees saves us
proving the CTL formula tediously by exploring the state space.\<close>
lemma gdpr_att: "gdpr_Kripke \<turnstile> EF {x. \<not>(global_policy' x ''Eve'')}"
proof -
  have a: " \<turnstile>([\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>)"
    by (rule att_gdpr)
  hence "(Igdpr,sgdpr) = attack ([\<N>\<^bsub>(Igdpr, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', sgdpr)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Igdpr, sgdpr)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Igdpr. i \<rightarrow>\<^sub>i* s} Igdpr \<turnstile> EF sgdpr"
    using ATV_EF gdpr_abs_att by fastforce 
  thus "gdpr_Kripke \<turnstile> EF {x::infrastructure. \<not> global_policy' x ''Eve''}"
    by (simp add: gdpr_Kripke_def gdpr_states_def Igdpr_def sgdpr_def)
qed

theorem gdpr_EF: "gdpr_Kripke \<turnstile> EF sgdpr"
  using gdpr_att sgdpr_def by blast 

text \<open>Similarly, vice-versa, the CTL statement proved in @{text \<open>gdpr_EF\<close>}
    can now be directly translated into Attack Trees using the Completeness 
    Theorem\footnote{This theorem could easily 
    be proved as a direct instance of @{text \<open>att_gdpr\<close>} above but we want to illustrate
    an alternative proof method using Completeness here.}.\<close>
theorem gdpr_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Igdpr,sgdpr)"
proof -
  have a: "gdpr_Kripke \<turnstile> EF sgdpr " by (rule gdpr_EF)
  have b: "Igdpr \<noteq> {}" by (simp add: Igdpr_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Igdpr, sgdpr)" 
  proof (rule Completeness)
    show "Kripke {s. \<exists>i\<in>Igdpr. i \<rightarrow>\<^sub>i* s} Igdpr \<turnstile> EF sgdpr"
      using a by (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
  qed (auto simp: Igdpr_def)
qed

text \<open>Conversely, since we have an attack given by rule @{text \<open>gdpr_AT\<close>}, we can immediately 
   infer @{text \<open>EF s\<close>} using Correctness @{text \<open>AT_EF\<close>}\footnote{Clearly, this theorem is identical
   to @{text \<open>gdpr_EF\<close>} and could thus be inferred from that one but we want to show here an 
   alternative way of proving it using the Correctness theorem @{text \<open>AT_EF\<close>}.}.\<close>
theorem gdpr_EF': "gdpr_Kripke \<turnstile> EF sgdpr"
  using gdpr_AT by (auto simp: gdpr_Kripke_def gdpr_states_def Igdpr_def dest: AT_EF)


(* However, when integrating DLM into the model and hence labeling
   information becomes part of the conditions of the get_data rule this isn't
   possible any more: gdpr_EF is not true any more *)    
(** GDPR properties  for the illustration of the DLM labeling **)    
section \<open>Data Protection by Design for GDPR compliance\<close>
subsection \<open>General Data Protection Regulation (GDPR)\<close>
text \<open>Since 26th May 2018, the GDPR has become mandatory within the European Union and hence 
also for any supplier of IT products. Breaches of the regulation will be fined with penalties 
of 20 Million EUR. Despite the relatively large size of the document of 209 pages, the technically 
relevant portion for us is only about 30 pages (Pages 81–111, Chapters I to Chapter III, Section 3). 
In summary, Chapter III specifies that the controller must give the data subject read access (1) 
to any information, communications, and “meta-data” of the data, e.g., retention time and purpose. 
In addition, the system must enable deletion of data (2) and restriction of processing.
An invariant condition for data processing resulting from these Articles is that the system functions 
must preserve any of the access rights of personal data (3).

Using labeled data, we can now express the essence of Article 4 Paragraph (1): 
’personal data’ means any information relating to an identified or identifiable natural 
person (’data subject’).

The labels of data must not be changed by processing: we have identified this  as 
an invariant (3) resulting from the GDPR above. This invariant is formalized in 
our Isabelle model by the type definition of functions on labeled data @{text \<open>label_fun\<close>}
(see Section 4.2) that preserve the data labels.\<close>

subsection \<open>Policy enforcement and privacy preservation\<close>
text \<open>We can now use the labeled data to encode the privacy constraints of the 
    GDPR in the rules. For example, the get data rule (see Section 4.3) has labelled data 
    @{text \<open>((Actor a’, as), n)\<close>} and uses the labeling in the precondition to guarantee 
    that only entitled users can get data.

We can prove that processing preserves ownership as defined in the initial state for all paths 
globally (AG) within the Kripke structure and in all locations of the graph.\<close>
(* GDPR three: Processing preserves ownership in any location *)    
lemma gdpr_three: "h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow>
         owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
         gdpr_Kripke \<turnstile> AG {x. \<forall> l \<in> gdpr_locations. owns (Igraph x) l (Actor h) d }"  
proof (simp add: gdpr_Kripke_def check_def, rule conjI)
  show "gdpr_scenario \<in> gdpr_states" by (simp add: gdpr_states_def state_transition_refl_def)
next 
  show "h \<in> gdpr_actors \<Longrightarrow>
    l \<in> gdpr_locations \<Longrightarrow>
    owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
    gdpr_scenario \<in> AG {x::infrastructure. \<forall>l\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}"
    apply (simp add: AG_def gfp_def)
    apply (rule_tac x = "{x::infrastructure. \<forall>l\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}" in exI)
    by (auto simp: AX_def gdpr_scenario_def owns_def)
qed

text \<open>The final application example of Correctness contraposition 
   shows that there is no attack to ownership possible.
The proved meta-theory for attack trees can be applied to facilitate the proof. 
The contraposition of the Correctness property grants that if there is no attack on 
@{text \<open>(I,\<not>f)\<close>}, then @{text \<open>(EF \<not>f)\<close>} does not hold in the Kripke structure. This 
yields the theorem since the @{text \<open>AG f\<close>} statement corresponds to @{text \<open>\<not>(EF \<not>f)\<close>}.
\<close>
theorem no_attack_gdpr_three: 
"h \<in> gdpr_actors \<Longrightarrow> l \<in> gdpr_locations \<Longrightarrow> 
 owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
attack A = (Igdpr, -{x. \<forall> l \<in> gdpr_locations. owns (Igraph x) l (Actor h) d })
\<Longrightarrow> \<not> (\<turnstile> A)"
proof (rule_tac I = Igdpr and 
           s = "-{x::infrastructure. \<forall>l\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}" 
       in contrapos_corr)
  show "h \<in> gdpr_actors \<Longrightarrow>
    l \<in> gdpr_locations \<Longrightarrow>
    owns (Igraph gdpr_scenario) l (Actor h) d \<Longrightarrow>
    attack A = (Igdpr, - {x::infrastructure. \<forall>l\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}) \<Longrightarrow>
    \<not> (Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Igdpr. i \<rightarrow>\<^sub>i* s}
        Igdpr \<turnstile> EF (- {x::infrastructure. \<forall>l\<in>gdpr_locations. owns (Igraph x) l (Actor h) d}))"
    apply (rule AG_imp_notnotEF) 
     apply (simp add: gdpr_Kripke_def Igdpr_def gdpr_states_def)
    using Igdpr_def gdpr_Kripke_def gdpr_states_def gdpr_three by auto
qed
end
end