(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory WHATWHERE_Security
imports Strong_Security.Types
begin

locale WHATWHERE = 
fixes SR :: "('exp, 'id, 'val, 'com) TLSteps"
and E :: "('exp, 'id, 'val) Evalfunction"
and pp :: "'com \<Rightarrow> nat"
and DA :: "('id, 'd::order) DomainAssignment"
and lH :: "('d::order, 'exp) lHatches"

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


abbreviation SRabbr :: "('exp, 'id, 'val, 'com) TLSteps_curry"
("(1\<langle>_,/_\<rangle>) \<rightarrow>\<lhd>_\<rhd>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0,0] 81)
where
"\<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> \<equiv> ((c,m),\<alpha>,(p,m')) \<in> SR"


\<comment> \<open>function for obtaining the unique memory (state) after one step for a command and a memory (state)\<close>
definition NextMem :: "'com \<Rightarrow> ('id, 'val) State \<Rightarrow> ('id, 'val) State"
( "\<lbrakk>_\<rbrakk>'(_')" )
where
"\<lbrakk>c\<rbrakk>(m) \<equiv> (THE m'. (\<exists>p \<alpha>. \<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>))"

\<comment> \<open>function getting all escape hatches for some location\<close>
definition htchLoc :: "nat \<Rightarrow> ('d, 'exp) Hatches"
where
"htchLoc \<iota> \<equiv> {(d,e). (d,e,\<iota>) \<in> lH}"

\<comment> \<open>function for getting all escape hatches for some set of locations\<close>
definition htchLocSet :: "nat set \<Rightarrow> ('d, 'exp) Hatches"
where
"htchLocSet PP \<equiv> \<Union>{h. (\<exists>\<iota> \<in> PP. h = htchLoc \<iota>)}"

\<comment> \<open>predicate for (d,H)-equality\<close>
definition dH_equal :: "'d \<Rightarrow> ('d, 'exp) Hatches
  \<Rightarrow> ('id, 'val) State \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"
where
"dH_equal d H m m' \<equiv> (m =\<^bsub>d\<^esub> m' \<and> 
  (\<forall>(d',e) \<in> H. (d' \<le> d \<longrightarrow> (E e m = E e m'))))"

abbreviation dH_equal' :: "('id, 'val) State \<Rightarrow> 'd \<Rightarrow> ('d, 'exp) Hatches
  \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"
( "(_ \<sim>\<^bsub>_,_\<^esub> _)" )
where
"m \<sim>\<^bsub>d,H\<^esub> m' \<equiv> dH_equal d H m m'"

\<comment> \<open>predicate indicating that a command is not a d-declassification command\<close>
definition NDC :: "'d \<Rightarrow> 'com \<Rightarrow> bool"
where
"NDC d c \<equiv> (\<forall>m m'. m =\<^bsub>d\<^esub> m' \<longrightarrow> \<lbrakk>c\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>c\<rbrakk>(m'))"

\<comment> \<open>predicate indicating an 'immediate d-declassification command' for a set of escape hatches\<close>
definition IDC :: "'d \<Rightarrow> 'com \<Rightarrow> ('d, 'exp) Hatches \<Rightarrow> bool"
where
"IDC d c H \<equiv> (\<exists>m m'. m =\<^bsub>d\<^esub> m' \<and> 
  (\<not> \<lbrakk>c\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>c\<rbrakk>(m')))
  \<and> (\<forall>m m'. m \<sim>\<^bsub>d,H\<^esub> m' \<longrightarrow> \<lbrakk>c\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>c\<rbrakk>(m') )"

definition stepResultsinR :: "'com ProgramState \<Rightarrow> 'com ProgramState 
  \<Rightarrow> 'com Bisimulation_type \<Rightarrow> bool"
where
"stepResultsinR p p' R \<equiv> (p = None \<and> p' = None) \<or> 
  (\<exists>c c'. (p = Some c \<and> p' = Some c' \<and> ([c],[c']) \<in> R))"


definition dhequality_alternative ::  "'d \<Rightarrow> nat set \<Rightarrow> nat 
  \<Rightarrow> ('id, 'val) State \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"
where
"dhequality_alternative d PP \<iota> m m' \<equiv> m \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m' \<or>
            (\<not> (htchLoc \<iota>) \<subseteq> (htchLocSet PP))"

definition Strong_dlHPP_Bisimulation :: "'d \<Rightarrow> nat set 
  \<Rightarrow> 'com Bisimulation_type \<Rightarrow> bool"
where
"Strong_dlHPP_Bisimulation d PP R \<equiv> 
  (sym R) \<and> (trans R) \<and>
  (\<forall>(V,V') \<in> R. length V = length V') \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. 
    ((NDC d (V!i)) \<or> 
     (IDC d (V!i) (htchLoc (pp (V!i)))))) \<and>
  (\<forall>(V,V') \<in> R. \<forall>i < length V. \<forall>m1 m1' m2 \<alpha> p.
    ( \<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle> \<and> m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1')
    \<longrightarrow> (\<exists>p' \<alpha>' m2'. ( \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        (stepResultsinR p p' R) \<and> (\<alpha>,\<alpha>') \<in> R \<and> 
        (dhequality_alternative d PP (pp (V!i)) m2 m2'))))"


\<comment> \<open>predicate to define when a program is strongly secure\<close>
definition WHATWHERE_Secure :: "'com list \<Rightarrow> bool"
where
"WHATWHERE_Secure V \<equiv> (\<forall>d PP. 
  (\<exists>R. Strong_dlHPP_Bisimulation d PP R \<and> (V,V) \<in> R))"


\<comment> \<open>auxiliary lemma to obtain central strong (d,lH,PP)-Bisimulation property as Lemma
 in meta logic (allows instantiating all the variables manually if necessary)\<close>
lemma strongdlHPPB_aux: 
 "\<And>V V' m1 m1' m2 p i \<alpha>. \<lbrakk> Strong_dlHPP_Bisimulation d PP R;
  i < length V; (V,V') \<in> R; 
  \<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>; m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1' \<rbrakk>
 \<Longrightarrow> (\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle>
  \<and> stepResultsinR p p' R \<and> (\<alpha>,\<alpha>') \<in> R \<and> 
  (dhequality_alternative d PP (pp (V!i)) m2 m2'))"
  by (simp add: Strong_dlHPP_Bisimulation_def, fastforce)

\<comment> \<open>auxiliary lemma to obtain 'NDC or IDC' from strong (d,lH,PP)-Bisimulation as lemma
  in meta logic allowing instantiation of the variables\<close>
lemma strongdlHPPB_NDCIDCaux:
"\<And>V V' i. \<lbrakk>Strong_dlHPP_Bisimulation d PP R;
  (V,V') \<in> R; i < length V \<rbrakk>
        \<Longrightarrow> (NDC d (V!i) \<or> IDC d (V!i) (htchLoc (pp (V!i))))"
  by (simp add: Strong_dlHPP_Bisimulation_def, auto)

lemma WHATWHERE_empty:
"WHATWHERE_Secure []"
  by (simp add: WHATWHERE_Secure_def, auto,
  rule_tac x="{([],[])}" in exI,
  simp add: Strong_dlHPP_Bisimulation_def sym_def trans_def)


end

end
