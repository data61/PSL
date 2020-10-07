theory CValue
imports C
begin

domain CValue
  = CFn (lazy "(C \<rightarrow> CValue) \<rightarrow> (C \<rightarrow> CValue)")
  | CB (lazy "bool discr")

fixrec CFn_project :: "CValue \<rightarrow> (C \<rightarrow> CValue) \<rightarrow> (C \<rightarrow> CValue)"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

lemma CFn_project_strict[simp]:
  "\<bottom> \<down>CFn v = \<bottom>"
  "CB\<cdot>b \<down>CFn v = \<bottom>"
  by (fixrec_simp)+

lemma CB_below[simp]: "CB\<cdot>b \<sqsubseteq> v \<longleftrightarrow> v = CB\<cdot>b"
  by (cases v) auto

fixrec CB_project :: "CValue \<rightarrow> CValue \<rightarrow> CValue \<rightarrow> CValue" where
  "CB_project\<cdot>(CB\<cdot>db)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if undiscr db then v\<^sub>1 else v\<^sub>2)"

lemma [simp]:
  "CB_project\<cdot>(CB\<cdot>(Discr b))\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if b then v\<^sub>1 else v\<^sub>2)"
  "CB_project\<cdot>\<bottom>\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
  "CB_project\<cdot>(CFn\<cdot>f)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
by fixrec_simp+

lemma CB_project_not_bot:
  "CB_project\<cdot>scrut\<cdot>v\<^sub>1\<cdot>v\<^sub>2 \<noteq> \<bottom> \<longleftrightarrow> (\<exists> b. scrut = CB\<cdot>(Discr b) \<and> (if b then v\<^sub>1 else v\<^sub>2) \<noteq> \<bottom>)"
  apply (cases scrut)
  apply simp
  apply simp
  by (metis (poly_guards_query) CB_project.simps CValue.injects(2) discr.exhaust undiscr_Discr)

text \<open>HOLCF provides us @{const CValue_take}\<open>::\<close>@{typeof CValue_take};
we want a similar function for @{typ "C \<rightarrow> CValue"}.\<close>

abbreviation C_to_CValue_take :: "nat \<Rightarrow> (C \<rightarrow> CValue) \<rightarrow> (C \<rightarrow> CValue)"
   where "C_to_CValue_take n \<equiv> cfun_map\<cdot>ID\<cdot>(CValue_take n)"

lemma C_to_CValue_chain_take: "chain C_to_CValue_take"
  by (auto intro: chainI cfun_belowI chainE[OF CValue.chain_take] monofun_cfun_fun)

lemma C_to_CValue_reach: "(\<Squnion> n. C_to_CValue_take n\<cdot>x) = x"
  by (auto intro:  cfun_eqI simp add: contlub_cfun_fun[OF ch2ch_Rep_cfunL[OF C_to_CValue_chain_take]]  CValue.reach)


end
