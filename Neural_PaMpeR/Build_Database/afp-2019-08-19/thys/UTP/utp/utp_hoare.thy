section \<open> Relational Hoare calculus \<close>

theory utp_hoare
  imports 
    utp_rel_laws
    utp_theory
begin

subsection \<open> Hoare Triple Definitions and Tactics \<close>

definition hoare_r :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<^sub>u") where
"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = ((\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

declare hoare_r_def [upred_defs]

named_theorems hoare and hoare_safe

method hoare_split uses hr = 
  ((simp add: assigns_comp)?, \<comment> \<open> Combine Assignments where possible \<close>
   (auto
    intro: hoare intro!: hoare_safe hr
    simp add: conj_comm conj_assoc usubst unrest))[1] \<comment> \<open> Apply Hoare logic laws \<close>

method hoare_auto uses hr = (hoare_split hr: hr; (rel_simp)?, auto?)

subsection \<open> Basic Laws \<close>

lemma hoare_meaning:
  "\<lbrace>P\<rbrace>S\<lbrace>Q\<rbrace>\<^sub>u = (\<forall> s s'. \<lbrakk>P\<rbrakk>\<^sub>e s \<and> \<lbrakk>S\<rbrakk>\<^sub>e (s, s') \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s')"
  by (rel_auto)

lemma hoare_assume: "\<lbrace>P\<rbrace>S\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> ?[P] ;; S = ?[P] ;; S ;; ?[Q]"
  by (rel_auto)

lemma hoare_r_conj [hoare_safe]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u; \<lbrace>p\<rbrace>Q\<lbrace>s\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<lbrace>r \<and> s\<rbrace>\<^sub>u"
  by rel_auto

lemma hoare_r_weaken_pre [hoare]:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u"
  "\<lbrace>q\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u"
  by rel_auto+

lemma pre_str_hoare_r:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u" 
  using assms by rel_auto
    
lemma post_weak_hoare_r:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>u" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>u" 
  using assms by rel_auto

lemma hoare_r_conseq: "\<lbrakk> `p\<^sub>1 \<Rightarrow> p\<^sub>2`; \<lbrace>p\<^sub>2\<rbrace>S\<lbrace>q\<^sub>2\<rbrace>\<^sub>u; `q\<^sub>2 \<Rightarrow> q\<^sub>1` \<rbrakk> \<Longrightarrow> \<lbrace>p\<^sub>1\<rbrace>S\<lbrace>q\<^sub>1\<rbrace>\<^sub>u"
  by rel_auto

subsection \<open> Assignment Laws \<close>

lemma assigns_hoare_r [hoare_safe]: "`p \<Rightarrow> \<sigma> \<dagger> q` \<Longrightarrow> \<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

lemma assigns_backward_hoare_r: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

lemma assign_floyd_hoare_r:
  assumes "vwb_lens x"
  shows "\<lbrace>p\<rbrace> assign_r x e \<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>u"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma assigns_init_hoare [hoare_safe]:
  "\<lbrakk> vwb_lens x; x \<sharp> p; x \<sharp> v; \<lbrace>&x =\<^sub>u v \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x := v ;; S\<lbrace>q\<rbrace>\<^sub>u"
  by (rel_auto)

lemma skip_hoare_r [hoare_safe]: "\<lbrace>p\<rbrace>II\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

lemma skip_hoare_impl_r [hoare_safe]: "`p \<Rightarrow> q` \<Longrightarrow> \<lbrace>p\<rbrace>II\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto  

subsection \<open> Sequence Laws \<close>

lemma seq_hoare_r: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>s\<rbrace>\<^sub>u ; \<lbrace>s\<rbrace>Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  by rel_auto

lemma seq_hoare_invariant [hoare_safe]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>u ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

lemma seq_hoare_stronger_pre_1 [hoare_safe]: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

lemma seq_hoare_stronger_pre_2 [hoare_safe]: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto
    
lemma seq_hoare_inv_r_2 [hoare]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>q\<rbrace>\<^sub>u ; \<lbrace>q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

lemma seq_hoare_inv_r_3 [hoare]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>u ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

subsection \<open> Conditional Laws \<close>

lemma cond_hoare_r [hoare_safe]: "\<lbrakk> \<lbrace>b \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u ; \<lbrace>\<not>b \<and> p\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

lemma cond_hoare_r_wp: 
  assumes "\<lbrace>p'\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>p''\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>(b \<and> p') \<or> (\<not>b \<and> p'')\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q\<rbrace>\<^sub>u"
  using assms by pred_simp

lemma cond_hoare_r_sp:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>T\<lbrace>s\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>p\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q \<or> s\<rbrace>\<^sub>u\<close>
  using assms by pred_simp

subsection \<open> Recursion Laws \<close>

lemma nu_hoare_r_partial: 
  assumes induct_step:
    "\<And> st P. \<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>u"   
  shows "\<lbrace>p\<rbrace>\<nu> F \<lbrace>q\<rbrace>\<^sub>u"  
  by (meson hoare_r_def induct_step lfp_lowerbound order_refl)

lemma mu_hoare_r:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>u"   
  shows "\<lbrace>p\<rbrace>\<mu> F \<lbrace>q\<rbrace>\<^sub>u"  
  unfolding hoare_r_def
proof (rule mu_rec_total_utp_rule[OF WF M , of _ e ], goal_cases)
  case (1 st)
  then show ?case 
    using induct_step[unfolded hoare_r_def, of "(\<lceil>p\<rceil>\<^sub>< \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)" st]
    by (simp add: alpha)    
qed
    
lemma mu_hoare_r':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>u" 
  assumes I0: "`p' \<Rightarrow> p`"  
  shows "\<lbrace>p'\<rbrace> \<mu> F \<lbrace>q\<rbrace>\<^sub>u"
  by (meson I0 M WF induct_step mu_hoare_r pre_str_hoare_r)

subsection \<open> Iteration Rules \<close>

lemma iter_hoare_r: "\<lbrace>P\<rbrace>S\<lbrace>P\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>S\<^sup>\<star>\<lbrace>P\<rbrace>\<^sub>u"
  by (rel_simp', metis (mono_tags, lifting) mem_Collect_eq rtrancl_induct)

lemma while_hoare_r [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>while b do S od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
  using assms
  by (simp add: while_top_def hoare_r_def, rule_tac lfp_lowerbound) (rel_auto)

lemma while_invr_hoare_r [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u" "`pre \<Rightarrow> p`" "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do S od\<lbrace>post\<rbrace>\<^sub>u"
  by (metis assms hoare_r_conseq while_hoare_r while_inv_def)

lemma while_r_minimal_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar\<and> b\<rbrace> C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  using induct_step pre_str_hoare_r seq_step while_hoare_r by blast

lemma approx_chain: 
  "(\<Sqinter>n::nat. \<lceil>p \<and> v <\<^sub>u \<guillemotleft>n\<guillemotright>\<rceil>\<^sub><) = \<lceil>p\<rceil>\<^sub><"
  by (rel_auto)

text \<open> Total correctness law for Hoare logic, based on constructive chains. This is limited to
  variants that have naturals numbers as their range. \<close>
    
lemma while_term_hoare_r:
  assumes "\<And> z::nat. \<lbrace>p \<and> b \<and> v =\<^sub>u \<guillemotleft>z\<guillemotright>\<rbrace>S\<lbrace>p \<and> v <\<^sub>u \<guillemotleft>z\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom> b do S od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
proof -
  have "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<not> b \<and> p\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> X \<bullet> S ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
  proof (rule mu_refine_intro)

    from assms show "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<not> b \<and> p\<rceil>\<^sub>>) \<sqsubseteq> S ;; (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<not> b \<and> p\<rceil>\<^sub>>) \<triangleleft> b \<triangleright>\<^sub>r II"
      by (rel_auto)

    let ?E = "\<lambda> n. \<lceil>p \<and> v <\<^sub>u \<guillemotleft>n\<guillemotright>\<rceil>\<^sub><"
    show "(\<lceil>p\<rceil>\<^sub>< \<and> (\<mu> X \<bullet> S ;; X \<triangleleft> b \<triangleright>\<^sub>r II)) = (\<lceil>p\<rceil>\<^sub>< \<and> (\<nu> X \<bullet> S ;; X \<triangleleft> b \<triangleright>\<^sub>r II))"
    proof (rule constr_fp_uniq[where E="?E"])

      show "(\<Sqinter>n. ?E(n)) = \<lceil>p\<rceil>\<^sub><"
        by (rel_auto)
          
      show "mono (\<lambda>X. S ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
        by (simp add: cond_mono monoI seqr_mono)
          
      show "constr (\<lambda>X. S ;; X \<triangleleft> b \<triangleright>\<^sub>r II) ?E"
      proof (rule constrI)
        
        show "chain ?E"
        proof (rule chainI)
          show "\<lceil>p \<and> v <\<^sub>u \<guillemotleft>0\<guillemotright>\<rceil>\<^sub>< = false"
            by (rel_auto)
          show "\<And>i. \<lceil>p \<and> v <\<^sub>u \<guillemotleft>Suc i\<guillemotright>\<rceil>\<^sub>< \<sqsubseteq> \<lceil>p \<and> v <\<^sub>u \<guillemotleft>i\<guillemotright>\<rceil>\<^sub><"
            by (rel_auto)
        qed
          
        from assms
        show "\<And>X n. (S ;; X \<triangleleft> b \<triangleright>\<^sub>r II \<and> \<lceil>p \<and> v <\<^sub>u \<guillemotleft>n + 1\<guillemotright>\<rceil>\<^sub><) =
                     (S ;; (X \<and> \<lceil>p \<and> v <\<^sub>u \<guillemotleft>n\<guillemotright>\<rceil>\<^sub><) \<triangleleft> b \<triangleright>\<^sub>r II \<and> \<lceil>p \<and> v <\<^sub>u \<guillemotleft>n + 1\<guillemotright>\<rceil>\<^sub><)"
          apply (rel_auto)
          using less_antisym less_trans apply blast
          done
      qed  
    qed
  qed

  thus ?thesis
    by (simp add: hoare_r_def while_bot_def)
qed

lemma while_vrt_hoare_r [hoare_safe]:
  assumes "\<And> z::nat. \<lbrace>p \<and> b \<and> v =\<^sub>u \<guillemotleft>z\<guillemotright>\<rbrace>S\<lbrace>p \<and> v <\<^sub>u \<guillemotleft>z\<guillemotright>\<rbrace>\<^sub>u" "`pre \<Rightarrow> p`" "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p vrt v do S od\<lbrace>post\<rbrace>\<^sub>u"
  apply (rule hoare_r_conseq[OF assms(2) _ assms(3)])
  apply (simp add: while_vrt_def)
  apply (rule while_term_hoare_r[where v="v", OF assms(1)]) 
  done
  
text \<open> General total correctness law based on well-founded induction \<close>
        
lemma while_wf_hoare_r:
  assumes WF: "wf R"
  assumes I0: "`pre \<Rightarrow> p`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>Q\<lbrace>p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  assumes PHI:"`(\<not>b \<and> p) \<Rightarrow> post`"  
  shows "\<lbrace>pre\<rbrace>while\<^sub>\<bottom> b invr p do Q od\<lbrace>post\<rbrace>\<^sub>u"
unfolding hoare_r_def while_inv_bot_def while_bot_def
proof (rule pre_weak_rel[of _ "\<lceil>p\<rceil>\<^sub><" ])
  from I0 show "`\<lceil>pre\<rceil>\<^sub>< \<Rightarrow> \<lceil>p\<rceil>\<^sub><`"
    by rel_auto
  show "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> X \<bullet> Q ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
  proof (rule mu_rec_total_utp_rule[where e=e, OF WF])
    show "Monotonic (\<lambda>X. Q ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
      by (simp add: closure)
    have induct_step': "\<And> st. (\<lceil>b \<and> p \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright> \<rceil>\<^sub>< \<Rightarrow> (\<lceil>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<rceil>\<^sub>> )) \<sqsubseteq> Q"
      using induct_step by rel_auto  
    with PHI
    show "\<And>st. (\<lceil>p\<rceil>\<^sub>< \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<sqsubseteq> Q ;; (\<lceil>p\<rceil>\<^sub>< \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<triangleleft> b \<triangleright>\<^sub>r II" 
      by (rel_auto)
  qed       
qed

subsection \<open> Frame Rules \<close>

text \<open> Frame rule: If starting $S$ in a state satisfying $p establishes q$ in the final state, then
  we can insert an invariant predicate $r$ when $S$ is framed by $a$, provided that $r$ does not
  refer to variables in the frame, and $q$ does not refer to variables outside the frame. \<close>

lemma frame_hoare_r:
  assumes "vwb_lens a" "a \<sharp> r" "a \<natural> q" "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms
  by (rel_auto, metis)

lemma frame_strong_hoare_r [hoare_safe]: 
  assumes "vwb_lens a" "a \<sharp> r" "a \<natural> q" "\<lbrace>p \<and> r\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p \<and> r\<rbrace>a:[S]\<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms by (rel_auto, metis)

lemma frame_hoare_r' [hoare_safe]: 
  assumes "vwb_lens a" "a \<sharp> r" "a \<natural> q" "\<lbrace>r \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>r \<and> p\<rbrace>a:[S]\<lbrace>r \<and> q\<rbrace>\<^sub>u"
  using assms
  by (simp add: frame_strong_hoare_r utp_pred_laws.inf.commute)

lemma antiframe_hoare_r:
  assumes "vwb_lens a" "a \<natural> r" "a \<sharp> q" "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms by (rel_auto, metis)
    
lemma antiframe_strong_hoare_r:
  assumes "vwb_lens a" "a \<natural> r" "a \<sharp> q" "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms by (rel_auto, metis)
  
end