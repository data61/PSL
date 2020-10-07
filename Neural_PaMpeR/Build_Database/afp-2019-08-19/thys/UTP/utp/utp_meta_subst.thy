section \<open> Meta-level Substitution \<close>

theory utp_meta_subst
imports utp_subst utp_tactics
begin

text \<open> Meta substitution substitutes a HOL variable in a UTP expression for another UTP expression.
  It is analogous to UTP substitution, but acts on functions. \<close>
  
lift_definition msubst :: "('b \<Rightarrow> ('a, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr"
is "\<lambda> F v b. F (v b) b" .
  
update_uexpr_rep_eq_thms \<comment> \<open> Reread @{text rep_eq} theorems. \<close>
    
syntax
  "_msubst"   :: "logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("(_\<lbrakk>_\<rightarrow>_\<rbrakk>)" [990,0,0] 991)

translations
  "_msubst P x v" == "CONST msubst (\<lambda> x. P) v"
     
lemma msubst_lit [usubst]: "\<guillemotleft>x\<guillemotright>\<lbrakk>x\<rightarrow>v\<rbrakk> = v"
  by (pred_auto)

lemma msubst_const [usubst]: "P\<lbrakk>x\<rightarrow>v\<rbrakk> = P"
  by (pred_auto) 

lemma msubst_pair [usubst]: "(P x y)\<lbrakk>(x, y) \<rightarrow> (e, f)\<^sub>u\<rbrakk> = (P x y)\<lbrakk>x \<rightarrow> e\<rbrakk>\<lbrakk>y \<rightarrow> f\<rbrakk>"
  by (rel_auto)

lemma msubst_lit_2_1 [usubst]: "\<guillemotleft>x\<guillemotright>\<lbrakk>(x,y)\<rightarrow>(u,v)\<^sub>u\<rbrakk> = u"
  by (pred_auto)

lemma msubst_lit_2_2 [usubst]: "\<guillemotleft>y\<guillemotright>\<lbrakk>(x,y)\<rightarrow>(u,v)\<^sub>u\<rbrakk> = v"
  by (pred_auto)

lemma msubst_lit' [usubst]: "\<guillemotleft>y\<guillemotright>\<lbrakk>x\<rightarrow>v\<rbrakk> = \<guillemotleft>y\<guillemotright>"
  by (pred_auto)

lemma msubst_lit'_2 [usubst]: "\<guillemotleft>z\<guillemotright>\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> = \<guillemotleft>z\<guillemotright>"
  by (pred_auto)
 
lemma msubst_uop [usubst]: "(uop f (v x))\<lbrakk>x\<rightarrow>u\<rbrakk> = uop f ((v x)\<lbrakk>x\<rightarrow>u\<rbrakk>)"
  by (rel_auto)

lemma msubst_uop_2 [usubst]: "(uop f (v x y))\<lbrakk>(x,y)\<rightarrow>u\<rbrakk> = uop f ((v x y)\<lbrakk>(x,y)\<rightarrow>u\<rbrakk>)"
  by (pred_simp, pred_simp)
 
lemma msubst_bop [usubst]: "(bop f (v x) (w x))\<lbrakk>x\<rightarrow>u\<rbrakk> = bop f ((v x)\<lbrakk>x\<rightarrow>u\<rbrakk>) ((w x)\<lbrakk>x\<rightarrow>u\<rbrakk>)"
  by (rel_auto)

lemma msubst_bop_2 [usubst]: "(bop f (v x y) (w x y))\<lbrakk>(x,y)\<rightarrow>u\<rbrakk> = bop f ((v x y)\<lbrakk>(x,y)\<rightarrow>u\<rbrakk>) ((w x y)\<lbrakk>(x,y)\<rightarrow>u\<rbrakk>)"
  by (pred_simp, pred_simp)

lemma msubst_var [usubst]:
  "(utp_expr.var x)\<lbrakk>y\<rightarrow>u\<rbrakk> = utp_expr.var x"
  by (pred_simp)

lemma msubst_var_2 [usubst]:
  "(utp_expr.var x)\<lbrakk>(y,z)\<rightarrow>u\<rbrakk> = utp_expr.var x"
  by (pred_simp)+
        
lemma msubst_unrest [unrest]: "\<lbrakk> \<And> v. x \<sharp> P(v); x \<sharp> k \<rbrakk> \<Longrightarrow> x \<sharp> P(v)\<lbrakk>v\<rightarrow>k\<rbrakk>"
  by (pred_auto)
  
end