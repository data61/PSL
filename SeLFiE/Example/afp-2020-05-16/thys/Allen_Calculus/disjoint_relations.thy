(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)


theory disjoint_relations

imports
  allen  

begin

section \<open>PD property\<close>
text \<open>The 13 time interval relations (i.e. e, b, m, s, f, d, ov and their inverse relations) are pairwise disjoint.\<close>


 (**e**)
lemma em (*[simp]*):"e \<inter> m = {}" 
using e m  meets_irrefl 
by (metis ComplI disjoint_eq_subset_Compl meets_wd subrelI)

lemma  eb (*[simp]*):"e \<inter> b = {}" 
using b e meets_asym 
by (metis ComplI disjoint_eq_subset_Compl subrelI)

lemma  eov (*[simp]*):"e \<inter> ov = {}" 
apply (auto simp: e ov)
using elimmeets by blast

lemma  es (*[simp]*):"e \<inter> s = {}" 
apply (auto simp:e s)
using elimmeets by blast

lemma  ef (*[simp]*):"e \<inter> f = {}" 
using e f by (metis (no_types, lifting) ComplI disjoint_eq_subset_Compl meets_atrans subrelI)

lemma  ed (*[simp]*):"e \<inter> d = {}" 
using e d by (metis (no_types, lifting) ComplI disjoint_eq_subset_Compl meets_atrans subrelI)

lemma  emi (*[simp]*):"e \<inter> m^-1 = {}" 
using converseE em e 
by (metis disjoint_iff_not_equal)

lemma  ebi (*[simp]*):"e \<inter> b^-1 = {}" 
using converseE eb e 
by (metis disjoint_iff_not_equal)

lemma  eovi (*[simp]*):"e \<inter> ov^-1 = {}" 
using converseE eov e 
by (metis disjoint_iff_not_equal)

lemma  esi (*[simp]*):"e \<inter> s^-1 = {}" 
using converseE es e 
by (metis disjoint_iff_not_equal)

lemma  efi (*[simp]*):"e \<inter> f^-1 = {}" 
using converseE ef e 
by (metis disjoint_iff_not_equal)

lemma edi (*[simp]*):"e \<inter> d^-1 = {}" 
using converseE ed e 
by (metis disjoint_iff_not_equal)


(**m**)
lemma  mb (*[simp]*):"m \<inter> b = {}"
using m b
apply auto
using elimmeets by blast

lemma  mov (*[simp]*): "m \<inter> ov = {}" 
apply (auto simp:m ov) 
by (meson M1 elimmeets)

lemma  ms (*[simp]*):"m \<inter> s = {}" 
apply (auto simp:m s)
by (meson M1 elimmeets)

lemma  mf (*[simp]*):"m \<inter> f = {}" 
apply (auto simp:m f)
using elimmeets by blast

lemma  md (*[simp]*):"m \<inter> d = {}" 
apply (auto simp: m d)
using trans2 by blast

lemma  mi (*[simp]*):"m \<inter> m^-1 = {}" 
apply (auto simp:m)
using converseE m meets_asym by blast

lemma  mbi (*[simp]*):"m \<inter> b^-1 = {}" 
apply (auto simp:mb) 
apply (auto simp: m b) 
using nontrans2 by blast

lemma movi (*[simp]*):"m \<inter> ov^-1 = {}" 
using m ov
apply auto
using trans2 by blast

lemma  msi (*[simp]*):"m \<inter> s^-1 = {}" 
apply (auto simp:m s)
by (meson M1 elimmeets)

lemma  mfi (*[simp]*):"m \<inter> f^-1 = {}" 
apply (auto simp:m f)
by (meson M1 elimmeets)

lemma  mdi (*[simp]*):"m \<inter> d^-1 = {}" 
apply (auto simp:m d)
using trans2 by blast

(**b**)
lemma bov (*[simp]*):"b \<inter> ov = {}" 
apply (auto simp:b ov)
by (meson M1 trans2)

lemma bs (*[simp]*):"b \<inter> s = {}" 
apply (auto simp:b s)
by (meson M1 trans2)

lemma  bf (*[simp]*):"b \<inter> f = {}" 
apply (auto simp: b f)
by (meson M1 trans2)

lemma bd (*[simp]*):"b \<inter> d = {}" 
apply (auto simp:b d)
by (meson M1 nonmeets4)

lemma  bmi (*[simp]*):"b \<inter> m^-1 = {}" 
using mbi by auto

lemma  bi (*[simp]*):"b \<inter> b^-1 = {}" 
apply (auto simp:b)
using M5exist_var3 trans2 by blast

lemma bovi (*[simp]*):"b \<inter> ov^-1 = {}" 
apply (auto simp:bov) 
apply (auto simp:b ov) 
by (meson M1 nontrans2)

lemma  bsi (*[simp]*):"b \<inter> s^-1 = {}" 
using bs apply auto using b s apply auto 
using trans2 by blast

lemma bfi (*[simp]*):"b \<inter> f^-1 = {}" 
using bf apply auto using b f apply auto 
using trans2 by blast

lemma  bdi (*[simp]*):"b \<inter> d^-1 = {}" 
apply (auto simp:bd) 
apply (auto simp:b d) 
using trans2 
using M1 nonmeets4 by blast


(**ov**)
lemma ovs (*[simp]*):"ov \<inter> s = {}" 
apply (auto simp:ov s)
by (meson M1 meets_atrans)

lemma ovf (*[simp]*):"ov \<inter> f = {}" 
apply (auto simp:ov f)
by (meson M1 meets_atrans)

lemma ovd (*[simp]*):"ov\<inter> d = {}" 
apply (auto simp:ov d)
by (meson M1 trans2)

lemma ovmi (*[simp]*):"ov \<inter> m^-1 = {}" 
using movi by auto

lemma  ovbi (*[simp]*):"ov \<inter> b^-1 = {}" 
using bovi by blast

lemma ovi (*[simp]*):"ov \<inter> ov^-1 = {}" 
apply (auto simp:ov)
by (meson M1 trans2)

lemma ovsi (*[simp]*):"ov \<inter> s^-1 = {}" 
apply (auto simp:ov s)
by (meson M1 elimmeets)

lemma ovfi (*[simp]*):"ov \<inter> f^-1 = {}" 
apply (auto simp:ov f) 
by (meson M1 elimmeets)

lemma ovdi (*[simp]*):"ov \<inter> d^-1 = {}" 
apply (auto simp:ov d) 
by (meson M1 trans2)

(**s**)
lemma  sf (*[simp]*):"s \<inter> f = {}" 
apply (auto simp:s f) 
by (metis M4 elimmeets)

lemma sd (*[simp]*):"s \<inter> d = {}" 
apply (auto simp:s d) 
by (metis M1 meets_atrans)

lemma smi (*[simp]*):"s \<inter> m^-1 = {}" 
using msi by auto

lemma  sbi (*[simp]*):"s \<inter> b^-1 = {}" 
using bsi by blast

lemma  sovi (*[simp]*):"s \<inter> ov^-1 = {}" 
using ovsi by auto

lemma  si (*[simp]*):"s \<inter> s^-1 = {}" 
apply (auto simp:s) 
by (meson M1 trans2)

lemma sfi (*[simp]*):"s \<inter> f^-1 = {}" 
apply (auto simp:s f)
by (metis M4 elimmeets)

lemma sdi (*[simp]*):"s\<inter> d^-1 = {}" 
apply (auto simp:s d)
by (meson M1 meets_atrans)


(**f**)
lemma fd (*[simp]*):"f \<inter> d = {}" 
apply (auto simp:f d)
by (meson M1 meets_atrans)

lemma fmi (*[simp]*):"f \<inter> m^-1 = {}" 
using mfi by auto

lemma  fbi (*[simp]*):"f \<inter> b^-1 = {}" 
using bfi converse_Int by auto

lemma fovi (*[simp]*):"f \<inter> ov^-1 = {}" 
  using ovfi by auto

lemma fsi (*[simp]*):"f \<inter> s^-1 = {}" 
using sfi by auto

lemma fi (*[simp]*):"f \<inter> f^-1 = {}" 
apply (auto simp:f) 
by (meson M1 trans2)

lemma fdi (*[simp]*):"f \<inter> d^-1 = {}" 
apply (auto simp:f d) 
by (meson M1 trans2)


(**d**)
lemma dmi (*[simp]*):"d \<inter> m^-1 = {}" 
using mdi by auto

lemma  dbi (*[simp]*):"d \<inter> b^-1 = {}" 
using bdi by blast

lemma dovi (*[simp]*):"d \<inter> ov^-1 = {}" 
using ovdi by auto

lemma  dsi (*[simp]*):"d \<inter> s^-1 = {}" 
using sdi by auto

lemma  dfi (*[simp]*):"d \<inter> f^-1 = {}" 
apply (auto simp:d f) 
by (meson M1 trans2)

lemma  di (*[simp]*):"d \<inter> d^-1 = {}" 
apply (auto simp:d) 
by (meson M1 trans2)

(**m^-1**)
lemma mibi (*[simp]*):"m^-1 \<inter> b^-1 = {}" 
using mb by auto

lemma miovi (*[simp]*):"m^-1 \<inter> ov^-1 = {}" 
using mov by auto

lemma misi (*[simp]*):"m^-1 \<inter> s^-1 = {}" 
using ms by auto

lemma mifi (*[simp]*):"m^-1 \<inter> f^-1 = {}" 
using mf by auto

lemma midi (*[simp]*):"m^-1 \<inter> d^-1 = {}" 
using md by auto


(**b^-1**)
lemma  bid (*[simp]*):"b^-1 \<inter> d = {}" 
by (simp add: dbi inf_sup_aci(1))

lemma  bimi (*[simp]*):"b^-1 \<inter> m^-1 = {}" 
using mibi by auto

lemma  biovi (*[simp]*):"b^-1 \<inter> ov^-1 = {}" 
using bov by blast

lemma  bisi (*[simp]*):"b^-1 \<inter> s^-1 = {}" 
using bs by blast

lemma bifi (*[simp]*):"b^-1 \<inter> f^-1 = {}" 
using bf by blast

lemma bidi (*[simp]*):"b^-1 \<inter> d^-1 = {}" 
using bd by blast

(** ov^-1**)
lemma ovisi (*[simp]*):"ov^-1 \<inter> s^-1 = {}"
using ovs by blast

lemma ovifi (*[simp]*):"ov^-1 \<inter> f^-1 = {}"
using ovf by blast

lemma ovidi (*[simp]*):"ov^-1 \<inter> d^-1 = {}"
using ovd by blast


(** s^-1 **)
lemma sifi (*[simp]*):"s^-1 \<inter> f^-1 = {}"
using sf by blast

lemma sidi (*[simp]*):"s^-1 \<inter> d^-1 = {}"
using sd by blast 

(** f^-1**)
lemma fidi (*[simp]*):"f^-1 \<inter> d^-1 = {}"
using fd by blast

lemma eei[simp]:"e^-1 =  e"
using e 
by (metis converse_iff subrelI subset_antisym)

lemma rdisj_sym:"A \<inter> B = {} \<Longrightarrow> B \<inter> A = {}"
by auto

subsection \<open>Intersection rules\<close>
named_theorems e_rules declare em[e_rules] and eb[e_rules] and eov[e_rules] and es[e_rules] and ef[e_rules] and ed[e_rules] and emi[e_rules] and ebi[e_rules] and eovi[e_rules] 
and esi[e_rules] and efi[e_rules] and edi[e_rules]

named_theorems m_rules declare em[THEN rdisj_sym, m_rules] and mb [m_rules] and ms  [m_rules] and mov [m_rules] and mf[m_rules] and 
md[m_rules] and mi [m_rules] and mbi [m_rules] and movi [m_rules] and msi [m_rules] and mfi [m_rules] and mdi [m_rules] and emi[m_rules]

named_theorems b_rules declare eb[THEN rdisj_sym, b_rules] and mb [THEN rdisj_sym, b_rules] and bs  [b_rules] and bov [b_rules] and bf[b_rules] and 
bd[b_rules] and bmi [b_rules] and bi [b_rules] and bovi [b_rules] and bsi [b_rules] and bfi [b_rules] and bdi [b_rules] and ebi[b_rules]

named_theorems ov_rules declare eov[THEN rdisj_sym, ov_rules] and mov [THEN rdisj_sym, ov_rules] and ovs  [ov_rules] and bov [THEN rdisj_sym,ov_rules] and ovf[ov_rules] and 
ovd[ov_rules] and ovmi [ov_rules] and  ovi [ov_rules] and ovsi [ov_rules] and ovfi [ov_rules] and ovdi [ov_rules] and eovi[ov_rules]

named_theorems s_rules declare es[THEN rdisj_sym, s_rules] and ms [THEN rdisj_sym, s_rules] and ovs  [THEN rdisj_sym, s_rules] and bs [THEN rdisj_sym,s_rules] and sf[s_rules] and 
sd[s_rules] and smi [s_rules] and  sovi [s_rules] and si [s_rules] and sfi [s_rules] and sdi [s_rules]

named_theorems d_rules declare ed[THEN rdisj_sym, d_rules] and md [THEN rdisj_sym, d_rules] and sd  [THEN rdisj_sym, d_rules]  and fd[THEN rdisj_sym, d_rules] and 
ovd[THEN rdisj_sym,d_rules] and dmi [d_rules] and  dovi [d_rules] and dsi [d_rules] and dfi [d_rules] and di [d_rules] 
 
named_theorems f_rules declare ef[THEN rdisj_sym, f_rules] and mf [THEN rdisj_sym, f_rules] and sf  [THEN rdisj_sym, f_rules] and ovf [THEN rdisj_sym,f_rules] and fd[f_rules] and 
 fmi [f_rules] and  fovi [f_rules] and fsi [f_rules] and fi [f_rules] and fdi [f_rules] 

 
end
