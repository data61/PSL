(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Type_System
imports Language_Composition
begin

locale Type_System =
  WWP?: WHATWHERE_Secure_Programs "E" "BMap" "DA" "lH"
  for E :: "('exp, 'id, 'val) Evalfunction"
  and BMap :: "'val \<Rightarrow> bool"
  and DA :: "('id, 'd::order) DomainAssignment"
  and lH :: "('d, 'exp) lHatches"
+ 
fixes
AssignSideCondition :: "'id \<Rightarrow> 'exp \<Rightarrow> nat \<Rightarrow> bool"
and WhileSideCondition :: "'exp \<Rightarrow> bool"
and IfSideCondition :: 
  "'exp \<Rightarrow> ('exp,'id) MWLsCom \<Rightarrow> ('exp,'id) MWLsCom \<Rightarrow> bool" 
assumes semAssignSC: "AssignSideCondition x e \<iota> \<Longrightarrow> 
  e \<equiv>\<^bsub>DA x,(htchLoc \<iota>)\<^esub> e \<and> (\<forall>m m' d \<iota>'. (m \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> m' \<and> 
  \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m'))
  \<longrightarrow> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m'))" 
and semWhileSC: "WhileSideCondition e \<Longrightarrow> \<forall>d. e \<equiv>\<^bsub>d\<^esub> e"
and semIfSC: "IfSideCondition e c1 c2 \<Longrightarrow> \<forall>d. e \<equiv>\<^bsub>d\<^esub> e"
begin

\<comment> \<open>Security typing rules for the language commands\<close>
inductive
ComSecTyping :: "('exp, 'id) MWLsCom \<Rightarrow> bool"
  ("\<turnstile>\<^bsub>\<C>\<^esub> _")
and ComSecTypingL :: "('exp,'id) MWLsCom list \<Rightarrow> bool"
   ("\<turnstile>\<^bsub>\<V>\<^esub> _")
where
Skip: "\<turnstile>\<^bsub>\<C>\<^esub> skip\<^bsub>\<iota>\<^esub>" |
Assign: "\<lbrakk> AssignSideCondition x e \<iota> \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> x :=\<^bsub>\<iota>\<^esub> e" |
Spawn: "\<lbrakk> \<turnstile>\<^bsub>\<V>\<^esub> V \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> spawn\<^bsub>\<iota>\<^esub> V" |
Seq: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c1; \<turnstile>\<^bsub>\<C>\<^esub> c2 \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> c1;c2" |
While: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c; WhileSideCondition b \<rbrakk> 
     \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> while\<^bsub>\<iota>\<^esub> b do c od" |
If: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c1; \<turnstile>\<^bsub>\<C>\<^esub> c2; IfSideCondition b c1 c2 \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi" |
Parallel: "\<lbrakk> \<forall>i < length V. \<turnstile>\<^bsub>\<C>\<^esub> V!i \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<V>\<^esub> V"

inductive_cases parallel_cases:
"\<turnstile>\<^bsub>\<V>\<^esub> V"

definition auxiliary_predicate
where
"auxiliary_predicate V \<equiv> unique_PPV V \<longrightarrow> WHATWHERE_Secure V" 

\<comment> \<open>soundness proof of abstract type system\<close>
theorem ComSecTyping_single_is_sound:
"\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c; unique_PPc c \<rbrakk>
  \<Longrightarrow> WHATWHERE_Secure [c]"
proof (induct rule: ComSecTyping_ComSecTypingL.inducts(1)
    [of _ _ "auxiliary_predicate"], simp_all add: auxiliary_predicate_def)
  fix \<iota>
  show "WHATWHERE_Secure [skip\<^bsub>\<iota>\<^esub>]"
    by (metis WHATWHERE_Secure_Skip)
next
  fix x e \<iota>
  assume "AssignSideCondition x e \<iota>"
  thus "WHATWHERE_Secure [x :=\<^bsub>\<iota>\<^esub> e]"
    by (metis WHATWHERE_Secure_Assign semAssignSC)
next
  fix V \<iota>
  assume IH: "unique_PPV V \<longrightarrow> WHATWHERE_Secure V"
  assume uniPPspawn: "unique_PPc (spawn\<^bsub>\<iota>\<^esub> V)"
  hence "unique_PPV V"
    by (simp add: unique_PPV_def unique_PPc_def)
  with IH have "WHATWHERE_Secure V"
    ..
  with uniPPspawn show "WHATWHERE_Secure [spawn\<^bsub>\<iota>\<^esub> V]"
    by (metis Compositionality_Spawn)
next
  fix c1 c2
  assume IH1: "unique_PPc c1 \<Longrightarrow> WHATWHERE_Secure [c1]"
  assume IH2: "unique_PPc c2 \<Longrightarrow> WHATWHERE_Secure [c2]"
  assume uniPPc1c2: "unique_PPc (c1;c2)"
  from uniPPc1c2 have uniPPc1: "unique_PPc c1"
    by (simp add: unique_PPc_def)
  with IH1 have IS1: "WHATWHERE_Secure [c1]"
    .
  from uniPPc1c2 have uniPPc2: "unique_PPc c2"
    by (simp add: unique_PPc_def)
  with IH2 have IS2: "WHATWHERE_Secure [c2]"
    .

  from IS1 IS2 uniPPc1c2 show "WHATWHERE_Secure [c1;c2]"
    by (metis Compositionality_Seq)
next
  fix c b \<iota>
  assume SC: "WhileSideCondition b"
  assume IH: "unique_PPc c \<Longrightarrow> WHATWHERE_Secure [c]"
  assume uniPPwhile: "unique_PPc (while\<^bsub>\<iota>\<^esub> b do c od)"
  hence "unique_PPc c"
    by (simp add: unique_PPc_def)
  with IH have "WHATWHERE_Secure [c]"
    .
  with uniPPwhile SC show "WHATWHERE_Secure [while\<^bsub>\<iota>\<^esub> b do c od]"
    by (metis Compositionality_While semWhileSC)
next
  fix c1 c2 b \<iota>
  assume SC: "IfSideCondition b c1 c2"  
  assume IH1: "unique_PPc c1 \<Longrightarrow> WHATWHERE_Secure [c1]"
  assume IH2: "unique_PPc c2 \<Longrightarrow> WHATWHERE_Secure [c2]"
  assume uniPPif: "unique_PPc (if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi)"
  from uniPPif have "unique_PPc c1"
    by (simp add: unique_PPc_def)
  with IH1 have IS1: "WHATWHERE_Secure [c1]"
    .
  from uniPPif have "unique_PPc c2"
    by (simp add: unique_PPc_def)
  with IH2 have IS2: "WHATWHERE_Secure [c2]"
    .
  from IS1 IS2 SC uniPPif show 
    "WHATWHERE_Secure [if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi]"
    by (metis Compositionality_If semIfSC)
next
  fix V
  assume IH: "\<forall>i < length V. \<turnstile>\<^bsub>\<C>\<^esub> V ! i \<and>
    (unique_PPc (V!i) \<longrightarrow> WHATWHERE_Secure [V!i])"
  have "unique_PPV V \<longrightarrow> (\<forall>i < length V. unique_PPc (V!i))"
    by (metis uniPPV_uniPPc)
  with IH have "unique_PPV V \<longrightarrow> (\<forall>i < length V. WHATWHERE_Secure [V!i])" 
    by auto
  thus uniPPV: "unique_PPV V \<longrightarrow> WHATWHERE_Secure V"
    by (metis parallel_composition)
qed


theorem ComSecTyping_list_is_sound:
"\<lbrakk> \<turnstile>\<^bsub>\<V>\<^esub> V; unique_PPV V \<rbrakk> \<Longrightarrow> WHATWHERE_Secure V"
by (metis ComSecTyping_single_is_sound parallel_cases 
  parallel_composition uniPPV_uniPPc)
  
end

end
