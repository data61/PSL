(*
Title:  Allen's Interval Algebra 
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)


theory examples


imports

  disjoint_relations

begin

section \<open>Examples\<close>
subsection \<open>Compositions of non-basic relations\<close>
text\<open>Basic relations are the 13 time interval relations. The unions of basic relations are also relations and their compositions is the union of compositions.
We prove few of these compositions that are required in theory nest.thy.\<close>

method (in arelations) e_compose = (match conclusion in "e O b \<subseteq> _"   \<Rightarrow> \<open>insert ceb, blast\<close>  
                                      \<bar> _ \<Rightarrow> \<open>match conclusion in "e O m \<subseteq> _"  \<Rightarrow> \<open>insert cem, blast\<close> \<bar> _ \<Rightarrow> \<open>fail\<close>\<close>)

declare [[simp_trace_depth_limit=4]] 

lemma eovisidifmifiOm:"(e \<union>  ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> m\<inverse> \<union> f^-1) O m \<subseteq> m \<union> ov \<union> f^-1 \<union> d^-1 \<union> s \<union> s\<inverse> \<union> e" 
apply (simp, intro conjI)
  using cem apply blast
    using crm_rules by auto
 

lemma ovsmfidiesiOmi:"(ov \<union> s\<union> m  \<union> f^-1 \<union> d^-1 \<union> e \<union> s^-1) O m^-1 \<subseteq> d^-1 \<union> s^-1 \<union>  ov^-1 \<union> m^-1 \<union> f^-1 \<union> f \<union> e "
apply (simp, intro conjI)
  using crmi_rules by auto
 

lemma ovsmfidiesiOm:"(ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>) O m \<subseteq> b \<union> ov \<union> f^-1 \<union> d^-1 \<union> m "
apply (simp, intro conjI)
  using crm_rules by auto
  

lemma ovsmfidiesiOssie:"(ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>) O (s \<union> s^-1 \<union> e) \<subseteq> ov \<union> f^-1 \<union> d^-1 \<union> s \<union> e \<union> s^-1 \<union> m "
apply (simp, intro conjI)
  using crs_rules apply auto[7]
    using crsi_rules apply auto[7]
      using cre_rules by auto[7]

lemma " (b \<union> m \<union> ov \<union> s \<union> d) O (b \<union> m \<union> ov \<union> s \<union> d) \<subseteq>  b \<union> m \<union> ov \<union> s \<union> d"
apply (simp, intro conjI)
 using crb_rules apply auto[5]
  using crm_rules apply auto[5]
    using crov_rules apply auto[5]
      using crs_rules apply auto[5]
        using crd_rules by auto[5]

lemma ebmovovissifsiddib:"(e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>) O b \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
apply (simp, intro conjI)
   using crb_rules by auto
    

lemma ebmovovissiffiddibmovsd:"(e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>) O ( b \<union> m \<union> ov \<union> s \<union> d) \<subseteq> (b \<union> m \<union> ov \<union> s \<union> d \<union> f^-1 \<union> d^-1 \<union> ov^-1 \<union> s\<inverse> \<union> f \<union> e) "
apply (simp, intro conjI)
  using crb_rules apply auto[11]
    using crm_rules apply auto[11]
      using crov_rules apply auto[11]
        using crs_rules apply auto[11]
          using crd_rules by auto

lemma difimov:"(d^-1 \<union> f^-1 \<union> ov \<union> e \<union> f \<union> m \<union> b \<union> s^-1 \<union> s) O ( m \<union> ov \<union> s \<union> d \<union> b \<union> f^-1 \<union> f \<union> e) \<subseteq> ( e \<union> b \<union> m \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>)"
apply (simp, intro conjI)
  using crm_rules apply auto[9]
    using crov_rules apply auto[9]
      using crs_rules apply auto[9]
        using crd_rules apply auto[9]
          using crb_rules apply auto[9]
            using crfi_rules apply auto[9]
              using crf_rules apply auto[9]
                using cre_rules by auto

lemma difibs:"(d\<inverse> \<union> f\<inverse> \<union> ov \<union> e \<union> f \<union> m \<union> b \<union> s\<inverse> \<union> s) O (b \<union> s \<union> m) \<subseteq> (b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> \<union> d \<union> e \<union> s \<union> s\<inverse>)"
apply (simp, intro conjI)
  using crb_rules apply auto[9]
    using crs_rules apply auto[9]
      using crm_rules by auto
     
lemma bebmovovissiffiddi:"b O (e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>) \<subseteq> (b \<union> m \<union> ov \<union> s \<union> d)"
apply (simp, intro conjI)
  using cb_rules by auto[11]

lemma ovsmfidiesi:"(((ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>) O (ov^-1 \<union> s^-1 \<union> m^-1 \<union> f \<union> d \<union> e \<union> s)) \<subseteq> (s \<union> s^-1 \<union> f \<union> f^-1 \<union> d \<union> d^-1 \<union> e \<union> ov \<union> ov^-1 \<union> m \<union> m^-1))"
apply (simp, intro conjI)
  using crovi_rules apply auto[7]
    using crsi_rules apply auto[7]
      using crmi_rules apply auto[7]
        using crf_rules apply auto[7]
          using crd_rules apply auto[7]
            using cre_rules apply auto[7]  
              using crs_rules by auto                    

lemma piiq:"(p,i) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse> \<Longrightarrow> (i,q) \<in> ov^-1 \<union> s^-1 \<union> m^-1 \<union> f \<union> d \<union> e \<union> s \<Longrightarrow> (p,q) \<in> s \<union> s^-1 \<union> f \<union> f^-1 \<union> d \<union> d^-1 \<union> e \<union> ov \<union> ov^-1 \<union> m \<union> m^-1"     
using ovsmfidiesi relcomp.relcompI subsetCE by blast      


lemma  ceovisidiffimi_ffie:"(e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>) O (f \<union> f\<inverse> \<union> e) \<subseteq>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse> "    
apply (simp, intro conjI)
  using crf_rules apply auto[7]
    using crfi_rules apply auto[7]
      using cre_rules  by auto

lemma  ceovisidiffimi_ffie_simp:"(p,i) \<in> (e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>) \<Longrightarrow> (i, q) \<in> (f \<union> f\<inverse> \<union> e) \<Longrightarrow> (p,q) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse> "    
using ceovisidiffimi_ffie relcomp.relcompI subsetCE by blast      

lemma ceovisidiffimi_fife:" (e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>) O (f\<inverse> \<union> f \<union> e)  \<subseteq>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>"
apply (simp, intro conjI)
 using cefi covifi csifi cdifi cffi  cfifi cmifi covifi csifi cdifi apply auto[7]
   using cef covif csif cdif cff cfif cmif apply auto[7]
     using cee covie csie cdie cfe cfie cmie by auto[7]
           
lemma "(x, j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse> \<Longrightarrow> (j, i) \<in> f\<inverse> \<union> f \<union> e \<Longrightarrow> (x, i) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>"
using ceovisidiffimi_ffie_simp by blast

lemma m_ovsmfidiesi:"m O (ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>) \<subseteq> b \<union> s \<union> m"
apply (simp, intro conjI)
 using cm_rules by auto

lemma ovsmfidiesi_d:"(ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>) O d \<subseteq>  e \<union>  s \<union> d \<union> ov \<union> ov^-1 \<union> s^-1 \<union> f \<union> f^-1  \<union> d^-1"
apply (simp, intro conjI)
  using crd_rules by auto[7]
    

lemma cbi_esdovovisiffidi:"b^-1 O (e \<union> s \<union> d \<union> ov \<union> ov\<inverse> \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d\<inverse>) \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d "
apply (simp, intro conjI)
  using cbi_rules by auto[9]
   
lemma cm_alpha1ialpha4mi:"m O  (e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>) \<subseteq>  m \<union> ov \<union> s \<union> d \<union> b \<union> f^-1 \<union> f \<union> e"
apply (simp, intro conjI)
using cm_rules by auto


lemma cbi_alpha1ialpha4mi:"b^-1 O ( e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>) \<subseteq>  b^-1"
apply (simp, intro conjI)
  using cbi_rules by auto

lemma cbeta2_beta2:"( b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>) O ( b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>) \<subseteq>  b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>"
apply (simp, intro conjI)
  using crb_rules apply auto[5]
    using crm_rules apply auto[5]
      using crov_rules apply auto[5]
        using crfi_rules apply auto[5]
          using crdi_rules by auto

lemma cbeta2_gammabm: "(b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>) O ( e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>) \<subseteq> ( e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>)"
apply (simp, intro conjI)
  using cre_rules apply auto[5]
    using crb_rules apply auto[5]
      using crm_rules apply auto[5]
        using crov_rules apply auto[5]
          using crovi_rules apply auto[5]
            using crs_rules apply auto[5]
              using crsi_rules apply auto[5]
                using crf_rules apply auto[5]
                  using crfi_rules apply auto[5]
                    using crd_rules apply auto[5]
                      using crdi_rules by auto

lemma calpha1_alpha1:"(b \<union> m \<union> ov \<union> s \<union> d) O ( b \<union> m \<union> ov \<union> s \<union> d) \<subseteq> ( b \<union> m \<union> ov \<union> s \<union> d)"
apply (simp, intro conjI)
  using crb_rules apply auto[5]
    using crm_rules apply auto[5]
      using crov_rules apply auto[5]
        using crs_rules apply auto[5]
          using crd_rules by auto
   
subsection \<open>Intersection of non-basic relations\<close>

lemma  inter_ov:
assumes  "(i,j) \<in>  (b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>) \<inter> (e \<union> b^-1 \<union> m^-1 \<union> ov^-1 \<union> ov \<union> s^-1 \<union> s \<union> f^-1 \<union> f \<union> d^-1 \<union> d) \<inter> (b \<union> m \<union> ov \<union> s \<union> d)" 
shows "(i,j) \<in> ov"
using assms apply auto 
 using b_rules apply auto[43]
  using e_rules apply auto[9]
   using b_rules apply auto[30]
    using m_rules apply auto[24]
     using b_rules apply auto[6]
      using m_rules apply auto[20]
       using f_rules apply auto[14]
        using d_rules by auto

lemma neq_beta2i_alpha2alpha5m:
assumes  "(q, j) \<in> b\<inverse> \<union> d \<union> f \<union> ov\<inverse> \<union> m\<inverse> " and " (q, j) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" 
shows  False
using assms apply auto
  using b_rules apply auto[7]
    using ov_rules apply auto[4]
      using d_rules apply auto[6]
        using s_rules apply auto[3]
          using f_rules apply auto[5]
            using m_rules apply auto[2]
              using ov_rules apply auto[4]
                using m_rules by auto

lemma neq_bi_alpha1ialpha4mi:
assumes "(q,i) \<in> b^-1" and " (q, i) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>"
shows False
using assms apply auto
  using b_rules by auto


end
