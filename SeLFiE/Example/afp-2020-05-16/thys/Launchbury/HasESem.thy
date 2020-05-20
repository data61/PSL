theory HasESem
imports "Nominal-HOLCF" "Env-HOLCF"
begin

text \<open>
A local to work abstract in the expression type and semantics.
\<close>

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> ('var::at_base \<Rightarrow> 'value) \<rightarrow> 'value::{pure,pcpo}" 
begin
  abbreviation ESem_syn ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [0,0] 110) where "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
end

locale has_ignore_fresh_ESem = has_ESem +
  assumes fv_supp: "supp e = atom ` (fv e :: 'b set)"
  assumes ESem_considers_fv: "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"

end
