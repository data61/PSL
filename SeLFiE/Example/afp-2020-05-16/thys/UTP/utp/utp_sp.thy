(*************************************************************************************************)
(* Project: The Isabelle/UTP Proof System                                                        *)
(* File: utp_sp.thy                                                                              *)
(* Authors: Yakoub Nemouchi (Virginia Tech, USA) and Simon Foster (University of York, UK)       *)
(* Emails: nemouchi@vt.edu and simon.foster@york.ac.uk                                           *)
(*************************************************************************************************)

section \<open> Strong Postcondition Calculus\<close>

theory utp_sp
imports utp_wp
begin

named_theorems sp

method sp_tac = (simp add: sp)

consts
  usp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "sp" 60)
  
definition sp_upred :: "'\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> cond" where
"sp_upred p Q = \<lfloor>(\<lceil>p\<rceil>\<^sub>> ;; Q) :: ('\<alpha>, '\<beta>) urel\<rfloor>\<^sub>>"

adhoc_overloading
  usp sp_upred

declare sp_upred_def [upred_defs]

lemma sp_false [sp]: "p sp false = false"
  by (rel_simp) 

lemma sp_true [sp]: "q \<noteq> false \<Longrightarrow> q sp true = true"
  by (rel_auto) 
    
lemma sp_assigns_r [sp]: 
  "vwb_lens x \<Longrightarrow> (p sp x := e ) = (\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)"
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put, metis vwb_lens.put_eq) 

lemma sp_it_is_post_condition:
  "\<lbrace>p\<rbrace>C\<lbrace>p sp C\<rbrace>\<^sub>u"
  by rel_blast
    
lemma sp_it_is_the_strongest_post:
  "`p sp C \<Rightarrow> Q`\<Longrightarrow>\<lbrace>p\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast
    
lemma sp_so:
  "`p sp C \<Rightarrow> Q` = \<lbrace>p\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast
    
theorem sp_hoare_link:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<longleftrightarrow> (r \<sqsubseteq> p sp Q)"
  by rel_auto   
                             
lemma sp_while_r [sp]: 
   assumes \<open>`pre \<Rightarrow> I`\<close> and \<open>\<lbrace>I \<and> b\<rbrace>C\<lbrace>I'\<rbrace>\<^sub>u\<close> and \<open>`I' \<Rightarrow> I`\<close>
   shows "(pre sp invar I while\<^sub>\<bottom> b do C od) = (\<not>b \<and> I)"
   unfolding sp_upred_def     
   oops  
     
theorem sp_eq_intro: "\<lbrakk>\<And>r. r sp P = r sp Q\<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)  
    
lemma wp_sp_sym:
  "`prog wp (true sp prog)`"
  by rel_auto
     
lemma it_is_pre_condition:"\<lbrace>C wp Q\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast    

lemma it_is_the_weakest_pre:"`P \<Rightarrow> C wp Q` = \<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast  

lemma s_pre:"`P \<Rightarrow> C wp Q`=\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast     

end