section \<open> Used-by \<close>

theory utp_usedby
  imports utp_unrest
begin

text \<open> The used-by predicate is the dual of unrestriction. It states that the given lens is an 
  upper-bound on the size of state space the given expression depends on. It is similar to stating
  that the lens is a valid alphabet for the predicate. For convenience, and because the predicate
  uses a similar form, we will reuse much of unrestriction's infrastructure. \<close>
  
consts
  usedBy :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

syntax
  "_usedBy" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<natural>" 20)
  
translations
  "_usedBy x p" == "CONST usedBy x p"                                           
  "_usedBy (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_usedBy (x +\<^sub>L y) P"

lift_definition usedBy_uexpr :: "('b \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> bool" 
is "\<lambda> x e. (\<forall> b b'. e (b' \<oplus>\<^sub>L b on x) = e b)" .

adhoc_overloading usedBy usedBy_uexpr
  
lemma usedBy_lit [unrest]: "x \<natural> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma usedBy_sublens:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<natural> P" "x \<subseteq>\<^sub>L y" "vwb_lens y"
  shows "y \<natural> P"
  using assms 
  by (transfer, auto, metis Lens_Order.lens_override_idem lens_override_def sublens_obs_get vwb_lens_mwb)

lemma usedBy_svar [unrest]: "x \<natural> P \<Longrightarrow> &x \<natural> P"
  by (transfer, simp add: lens_defs)
    
lemma usedBy_lens_plus_1 [unrest]: "x \<natural> P \<Longrightarrow> x;y \<natural> P"
  by (transfer, simp add: lens_defs)

lemma usedBy_lens_plus_2 [unrest]: "\<lbrakk> x \<bowtie> y; y \<natural> P \<rbrakk> \<Longrightarrow> x;y \<natural> P"
  by (transfer, auto simp add: lens_defs lens_indep_comm)
    
text \<open> Linking used-by to unrestriction: if x is used-by P, and x is independent of y, then
  P cannot depend on any variable in y. \<close>
    
lemma usedBy_indep_uses:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<natural> P" "x \<bowtie> y"
  shows "y \<sharp> P"
  using assms by (transfer, auto, metis lens_indep_get lens_override_def)

lemma usedBy_var [unrest]:
  assumes "vwb_lens x" "y \<subseteq>\<^sub>L x"
  shows "x \<natural> var y"
  using assms
  by (transfer, simp add: uexpr_defs pr_var_def)
     (metis lens_override_def sublens_obs_get vwb_lens_def wb_lens.get_put)    
  
lemma usedBy_uop [unrest]: "x \<natural> e \<Longrightarrow> x \<natural> uop f e"
  by (transfer, simp)

lemma usedBy_bop [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> bop f u v"
  by (transfer, simp)

lemma usedBy_trop [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v; x \<natural> w \<rbrakk> \<Longrightarrow> x \<natural> trop f u v w"
  by (transfer, simp)

lemma usedBy_qtop [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v; x \<natural> w; x \<natural> y \<rbrakk> \<Longrightarrow> x \<natural> qtop f u v w y"
  by (transfer, simp)

text \<open> For convenience, we also prove used-by rules for the bespoke operators on equality,
  numbers, arithmetic etc. \<close>
    
lemma usedBy_eq [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> u =\<^sub>u v"
  by (simp add: eq_upred_def, transfer, simp)

lemma usedBy_zero [unrest]: "x \<natural> 0"
  by (simp add: usedBy_lit zero_uexpr_def)

lemma usedBy_one [unrest]: "x \<natural> 1"
  by (simp add: one_uexpr_def usedBy_lit)

lemma usedBy_numeral [unrest]: "x \<natural> (numeral n)"
  by (simp add: numeral_uexpr_simp usedBy_lit)

lemma usedBy_sgn [unrest]: "x \<natural> u \<Longrightarrow> x \<natural> sgn u"
  by (simp add: sgn_uexpr_def usedBy_uop)

lemma usedBy_abs [unrest]: "x \<natural> u \<Longrightarrow> x \<natural> abs u"
  by (simp add: abs_uexpr_def usedBy_uop)

lemma usedBy_plus [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> u + v"
  by (simp add: plus_uexpr_def unrest)

lemma usedBy_uminus [unrest]: "x \<natural> u \<Longrightarrow> x \<natural> - u"
  by (simp add: uminus_uexpr_def unrest)

lemma usedBy_minus [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> u - v"
  by (simp add: minus_uexpr_def unrest)

lemma usedBy_times [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> u * v"
  by (simp add: times_uexpr_def unrest)

lemma usedBy_divide [unrest]: "\<lbrakk> x \<natural> u; x \<natural> v \<rbrakk> \<Longrightarrow> x \<natural> u / v"
  by (simp add: divide_uexpr_def unrest)
    
lemma usedBy_ulambda [unrest]:
  "\<lbrakk> \<And> x. v \<natural> F x \<rbrakk> \<Longrightarrow> v \<natural> (\<lambda> x \<bullet> F x)"
  by (transfer, simp)      

lemma unrest_var_sep [unrest]:
  "vwb_lens x \<Longrightarrow> x \<natural> &x:y"
  by (transfer, simp add: lens_defs)
    
end