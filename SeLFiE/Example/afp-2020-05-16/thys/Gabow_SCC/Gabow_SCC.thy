section \<open>Enumerating the SCCs of a Graph \label{sec:scc}\<close>
theory Gabow_SCC
imports Gabow_Skeleton
begin

text \<open>
  As a first variant, we implement an algorithm that computes a list of SCCs 
  of a graph, in topological order. This is the standard variant described by
  Gabow~\cite{Gabow2000}.
\<close>

section \<open>Specification\<close>
context fr_graph
begin
  text \<open>We specify a distinct list that covers all reachable nodes and
    contains SCCs in topological order\<close>

  definition "compute_SCC_spec \<equiv> SPEC (\<lambda>l. 
    distinct l \<and> \<Union>(set l) = E\<^sup>*``V0 \<and> (\<forall>U\<in>set l. is_scc E U) 
    \<and> (\<forall>i j. i<j \<and> j<length l \<longrightarrow> l!j \<times> l!i \<inter> E\<^sup>* = {}) )"
end

section \<open>Extended Invariant\<close>

locale cscc_invar_ext = fr_graph G
  for G :: "('v,'more) graph_rec_scheme" + 
  fixes l :: "'v set list" and D :: "'v set"
  assumes l_is_D: "\<Union>(set l) = D" \<comment> \<open>The output contains all done CNodes\<close>
  assumes l_scc: "set l \<subseteq> Collect (is_scc E)" \<comment> \<open>The output contains only SCCs\<close>
  assumes l_no_fwd: "\<And>i j. \<lbrakk>i<j; j<length l\<rbrakk> \<Longrightarrow> l!j \<times> l!i \<inter> E\<^sup>* = {}" 
    \<comment> \<open>The output contains no forward edges\<close>
begin
  lemma l_no_empty: "{}\<notin>set l" using l_scc by (auto simp: in_set_conv_decomp)
end
  
locale cscc_outer_invar_loc = outer_invar_loc G it D + cscc_invar_ext G l D
  for G :: "('v,'more) graph_rec_scheme" and it l D 
begin
  lemma locale_this: "cscc_outer_invar_loc G it l D" by unfold_locales
  lemma abs_outer_this: "outer_invar_loc G it D" by unfold_locales
end

locale cscc_invar_loc = invar_loc G v0 D0 p D pE + cscc_invar_ext G l D
  for G :: "('v,'more) graph_rec_scheme" and v0 D0 and l :: "'v set list" 
  and p D pE
begin
  lemma locale_this: "cscc_invar_loc G v0 D0 l p D pE" by unfold_locales
  lemma invar_this: "invar_loc G v0 D0 p D pE" by unfold_locales
end

context fr_graph
begin
  definition "cscc_outer_invar \<equiv> \<lambda>it (l,D). cscc_outer_invar_loc G it l D"
  definition "cscc_invar \<equiv> \<lambda>v0 D0 (l,p,D,pE). cscc_invar_loc G v0 D0 l p D pE"
end

section \<open>Definition of the SCC-Algorithm\<close>

context fr_graph
begin
  definition compute_SCC :: "'v set list nres" where
    "compute_SCC \<equiv> do {
      let so = ([],{});
      (l,D) \<leftarrow> FOREACHi cscc_outer_invar V0 (\<lambda>v0 (l,D0). do {
        if v0\<notin>D0 then do {
          let s = (l,initial v0 D0);

          (l,p,D,pE) \<leftarrow>
          WHILEIT (cscc_invar v0 D0)
            (\<lambda>(l,p,D,pE). p \<noteq> []) (\<lambda>(l,p,D,pE). 
          do {
            \<comment> \<open>Select edge from end of path\<close>
            (vo,(p,D,pE)) \<leftarrow> select_edge (p,D,pE);

            ASSERT (p\<noteq>[]);
            case vo of 
              Some v \<Rightarrow> do {
                if v \<in> \<Union>(set p) then do {
                  \<comment> \<open>Collapse\<close>
                  RETURN (l,collapse v (p,D,pE))
                } else if v\<notin>D then do {
                  \<comment> \<open>Edge to new node. Append to path\<close>
                  RETURN (l,push v (p,D,pE))
                } else RETURN (l,p,D,pE)
              }
            | None \<Rightarrow> do {
                \<comment> \<open>No more outgoing edges from current node on path\<close>
                ASSERT (pE \<inter> last p \<times> UNIV = {});
                let V = last p;
                let (p,D,pE) = pop (p,D,pE);
                let l = V#l;
                RETURN (l,p,D,pE)
              }
          }) s;
          ASSERT (p=[] \<and> pE={});
          RETURN (l,D)
        } else
          RETURN (l,D0)
      }) so;
      RETURN l
    }"
end

section \<open>Preservation of Invariant Extension\<close>
context cscc_invar_ext
begin
  lemma l_disjoint: 
    assumes A: "i<j" "j<length l"
    shows "l!i \<inter> l!j = {}"
  proof (rule disjointI)
    fix u
    assume "u\<in>l!i" "u\<in>l!j"
    with l_no_fwd A show False by auto
  qed

  corollary l_distinct: "distinct l"
    using l_disjoint l_no_empty
    by (metis distinct_conv_nth inf_idem linorder_cases nth_mem)
end

context fr_graph
begin
  definition "cscc_invar_part \<equiv> \<lambda>(l,p,D,pE). cscc_invar_ext G l D"

  lemma cscc_invarI[intro?]:
    assumes "invar v0 D0 PDPE"
    assumes "invar v0 D0 PDPE \<Longrightarrow> cscc_invar_part (l,PDPE)"
    shows "cscc_invar v0 D0 (l,PDPE)"
    using assms
    unfolding initial_def cscc_invar_def invar_def
    apply (simp split: prod.split_asm)
    apply intro_locales
    apply (simp add: invar_loc_def)
    apply (simp add: cscc_invar_part_def cscc_invar_ext_def)
    done

  thm cscc_invarI[of v_0 D_0 s l]

  lemma cscc_outer_invarI[intro?]:
    assumes "outer_invar it D"
    assumes "outer_invar it D \<Longrightarrow> cscc_invar_ext G l D"
    shows "cscc_outer_invar it (l,D)"
    using assms
    unfolding initial_def cscc_outer_invar_def outer_invar_def
    apply (simp split: prod.split_asm)
    apply intro_locales
    apply (simp add: outer_invar_loc_def)
    apply (simp add: cscc_invar_ext_def)
    done

  lemma cscc_invar_initial[simp, intro!]:
    assumes A: "v0\<in>it" "v0\<notin>D0"
    assumes INV: "cscc_outer_invar it (l,D0)"
    shows "cscc_invar_part (l,initial v0 D0)"
  proof -
    from INV interpret cscc_outer_invar_loc G it l D0 
      unfolding cscc_outer_invar_def by simp
    
    show ?thesis
      unfolding cscc_invar_part_def initial_def
      apply simp
      by unfold_locales
  qed

  lemma cscc_invar_pop:
    assumes INV: "cscc_invar v0 D0 (l,p,D,pE)"
    assumes "invar v0 D0 (pop (p,D,pE))"
    assumes NE[simp]: "p\<noteq>[]"
    assumes NO': "pE \<inter> (last p \<times> UNIV) = {}"
    shows "cscc_invar_part (last p # l, pop (p,D,pE))"
  proof -
    from INV interpret cscc_invar_loc G v0 D0 l p D pE 
      unfolding cscc_invar_def by simp

    have AUX_l_scc: "is_scc E (last p)"
      unfolding is_scc_pointwise
    proof safe
      {
        assume "last p = {}" thus False 
          using p_no_empty by (cases p rule: rev_cases) auto 
      }

      fix u v
      assume "u\<in>last p" "v\<in>last p"
      with p_sc[of "last p"] have "(u,v) \<in> (lvE \<inter> last p \<times> last p)\<^sup>*" by auto
      with lvE_ss_E show "(u,v)\<in>(E \<inter> last p \<times> last p)\<^sup>*"
        by (metis Int_mono equalityE rtrancl_mono_mp)
      
      fix u'
      assume "u'\<notin>last p" "(u,u')\<in>E\<^sup>*" "(u',v)\<in>E\<^sup>*"

      from \<open>u'\<notin>last p\<close> \<open>u\<in>last p\<close> \<open>(u,u')\<in>E\<^sup>*\<close>
        and rtrancl_reachable_induct[OF order_refl lastp_un_D_closed[OF NE NO']]
      have "u'\<in>D" by auto
      with \<open>(u',v)\<in>E\<^sup>*\<close> and rtrancl_reachable_induct[OF order_refl D_closed] 
      have "v\<in>D" by auto
      with \<open>v\<in>last p\<close> p_not_D show False by (cases p rule: rev_cases) auto
    qed

    {
      fix i j
      assume A: "i<j" "j<Suc (length l)"
      have "l ! (j - Suc 0) \<times> (last p # l) ! i \<inter> E\<^sup>* = {}"
      proof (rule disjointI, safe)
        fix u v
        assume "(u, v) \<in> E\<^sup>*" "u \<in> l ! (j - Suc 0)" "v \<in> (last p # l) ! i"
        from \<open>u \<in> l ! (j - Suc 0)\<close> A have "u\<in>\<Union>(set l)"
          by (metis Ex_list_of_length Suc_pred UnionI length_greater_0_conv 
            less_nat_zero_code not_less_eq nth_mem) 
        with l_is_D have "u\<in>D" by simp
        with rtrancl_reachable_induct[OF order_refl D_closed] \<open>(u,v)\<in>E\<^sup>*\<close> 
        have "v\<in>D" by auto

        show False proof cases
          assume "i=0" hence "v\<in>last p" using \<open>v \<in> (last p # l) ! i\<close> by simp
          with p_not_D \<open>v\<in>D\<close> show False by (cases p rule: rev_cases) auto
        next
          assume "i\<noteq>0" with \<open>v \<in> (last p # l) ! i\<close> have "v\<in>l!(i - 1)" by auto
          with l_no_fwd[of "i - 1" "j - 1"] 
            and \<open>u \<in> l ! (j - Suc 0)\<close> \<open>(u, v) \<in> E\<^sup>*\<close> \<open>i\<noteq>0\<close> A
          show False by fastforce 
        qed
      qed
    } note AUX_l_no_fwd = this

    show ?thesis
      unfolding cscc_invar_part_def pop_def apply simp
      apply unfold_locales
      apply clarsimp_all
      using l_is_D apply auto []

      using l_scc AUX_l_scc apply auto []

      apply (rule AUX_l_no_fwd, assumption+) []
      done
  qed

  thm cscc_invar_pop[of v_0 D_0 l p D pE]

  lemma cscc_invar_unchanged: 
    assumes INV: "cscc_invar v0 D0 (l,p,D,pE)"
    shows "cscc_invar_part (l,p',D,pE')"
    using INV unfolding cscc_invar_def cscc_invar_part_def cscc_invar_loc_def
    by simp

  corollary cscc_invar_collapse:
    assumes INV: "cscc_invar v0 D0 (l,p,D,pE)"
    shows "cscc_invar_part (l,collapse v (p',D,pE'))"
    unfolding collapse_def
    by (simp add: cscc_invar_unchanged[OF INV])

  corollary cscc_invar_push:
    assumes INV: "cscc_invar v0 D0 (l,p,D,pE)"
    shows "cscc_invar_part (l,push v (p',D,pE'))"
    unfolding push_def
    by (simp add: cscc_invar_unchanged[OF INV])


  lemma cscc_outer_invar_initial: "cscc_invar_ext G [] {}"
    by unfold_locales auto


  lemma cscc_invar_outer_newnode:
    assumes A: "v0\<notin>D0" "v0\<in>it" 
    assumes OINV: "cscc_outer_invar it (l,D0)"
    assumes INV: "cscc_invar v0 D0 (l',[],D',pE)"
    shows "cscc_invar_ext G l' D'"
  proof -
    from OINV interpret cscc_outer_invar_loc G it l D0 
      unfolding cscc_outer_invar_def by simp
    from INV interpret inv: cscc_invar_loc G v0 D0 l' "[]" D' pE 
      unfolding cscc_invar_def by simp
    
    show ?thesis 
      by unfold_locales

  qed

  lemma cscc_invar_outer_Dnode:
    assumes "cscc_outer_invar it (l, D)"
    shows "cscc_invar_ext G l D"
    using assms
    by (simp add: cscc_outer_invar_def cscc_outer_invar_loc_def)
    
  lemmas cscc_invar_preserve = invar_preserve
    cscc_invar_initial
    cscc_invar_pop cscc_invar_collapse cscc_invar_push cscc_invar_unchanged 
    cscc_outer_invar_initial cscc_invar_outer_newnode cscc_invar_outer_Dnode

  text \<open>On termination, the invariant implies the specification\<close>
  lemma cscc_finI:
    assumes INV: "cscc_outer_invar {} (l,D)"
    shows fin_l_is_scc: "\<lbrakk>U\<in>set l\<rbrakk> \<Longrightarrow> is_scc E U"
    and fin_l_distinct: "distinct l"
    and fin_l_is_reachable: "\<Union>(set l) = E\<^sup>* `` V0"
    and fin_l_no_fwd: "\<lbrakk>i<j; j<length l\<rbrakk> \<Longrightarrow> l!j \<times>l!i \<inter> E\<^sup>* = {}"
  proof -
    from INV interpret cscc_outer_invar_loc G "{}" l D
      unfolding cscc_outer_invar_def by simp

    show "\<lbrakk>U\<in>set l\<rbrakk> \<Longrightarrow> is_scc E U" using l_scc by auto

    show "distinct l" by (rule l_distinct)

    show "\<Union>(set l) = E\<^sup>* `` V0"
      using fin_outer_D_is_reachable[OF outer_invar_this] l_is_D
      by auto

    show "\<lbrakk>i<j; j<length l\<rbrakk> \<Longrightarrow> l!j \<times>l!i \<inter> E\<^sup>* = {}"
      by (rule l_no_fwd)

  qed

end

section \<open>Main Correctness Proof\<close>

context fr_graph 
begin
  lemma invar_from_cscc_invarI: "cscc_invar v0 D0 (L,PDPE) \<Longrightarrow> invar v0 D0 PDPE"
    unfolding cscc_invar_def invar_def
    apply (simp split: prod.splits)
    unfolding cscc_invar_loc_def by simp

  lemma outer_invar_from_cscc_invarI: 
    "cscc_outer_invar it (L,D) \<Longrightarrow>outer_invar it D"
    unfolding cscc_outer_invar_def outer_invar_def
    apply (simp split: prod.splits)
    unfolding cscc_outer_invar_loc_def by simp

  text \<open>With the extended invariant and the auxiliary lemmas, the actual 
    correctness proof is straightforward:\<close>
  theorem compute_SCC_correct: "compute_SCC \<le> compute_SCC_spec"
  proof -
    note [[goals_limit = 2]]
    note [simp del] = Union_iff

    show ?thesis
      unfolding compute_SCC_def compute_SCC_spec_def select_edge_def select_def
      apply (refine_rcg
        WHILEIT_rule[where R="inv_image (abs_wf_rel v0) snd" for v0]
        refine_vcg 
      )

      apply (vc_solve
        rec: cscc_invarI cscc_outer_invarI
        solve: cscc_invar_preserve cscc_finI
        intro: invar_from_cscc_invarI outer_invar_from_cscc_invarI
        dest!: sym[of "pop A" for A]
        simp: pE_fin'[OF invar_from_cscc_invarI] finite_V0
      )
      apply auto
      done
  qed


  text \<open>Simple proof, for presentation\<close>
  context 
    notes [refine]=refine_vcg
    notes [[goals_limit = 1]]
  begin
    theorem "compute_SCC \<le> compute_SCC_spec"
      unfolding compute_SCC_def compute_SCC_spec_def select_edge_def select_def
      by (refine_rcg 
        WHILEIT_rule[where R="inv_image (abs_wf_rel v0) snd" for v0])
      (vc_solve 
        rec: cscc_invarI cscc_outer_invarI solve: cscc_invar_preserve cscc_finI
        intro: invar_from_cscc_invarI outer_invar_from_cscc_invarI
        dest!: sym[of "pop A" for A]
        simp: pE_fin'[OF invar_from_cscc_invarI] finite_V0, auto)
  end

end


section \<open>Refinement to Gabow's Data Structure\<close>

context GS begin
  definition "seg_set_impl l u \<equiv> do {
    (_,res) \<leftarrow> WHILET
      (\<lambda>(l,_). l<u) 
      (\<lambda>(l,res). do { 
        ASSERT (l<length S); 
        let x = S!l;
        ASSERT (x\<notin>res); 
        RETURN (Suc l,insert x res)
      }) 
      (l,{});
      
    RETURN res
  }"

  lemma seg_set_impl_aux:
    fixes l u
    shows "\<lbrakk>l<u; u\<le>length S; distinct S\<rbrakk> \<Longrightarrow> seg_set_impl l u 
    \<le> SPEC (\<lambda>r. r = {S!j | j. l\<le>j \<and> j<u})"
    unfolding seg_set_impl_def
    apply (refine_rcg 
      WHILET_rule[where 
        I="\<lambda>(l',res). res = {S!j | j. l\<le>j \<and> j<l'} \<and> l\<le>l' \<and> l'\<le>u"
        and R="measure (\<lambda>(l',_). u-l')" 
      ]
      refine_vcg)

    apply (auto simp: less_Suc_eq nth_eq_iff_index_eq)
    done

  lemma (in GS_invar) seg_set_impl_correct:
    assumes "i<length B"
    shows "seg_set_impl (seg_start i) (seg_end i) \<le> SPEC (\<lambda>r. r=p_\<alpha>!i)"
    apply (refine_rcg order_trans[OF seg_set_impl_aux] refine_vcg)

    using assms 
    apply (simp_all add: seg_start_less_end seg_end_bound S_distinct) [3]

    apply (auto simp: p_\<alpha>_def assms seg_def) []
    done

  definition "last_seg_impl 
    \<equiv> do {
      ASSERT (length B - 1 < length B);
      seg_set_impl (seg_start (length B - 1)) (seg_end (length B - 1))
    }"

  lemma (in GS_invar) last_seg_impl_correct:
    assumes "p_\<alpha> \<noteq> []"
    shows "last_seg_impl \<le> SPEC (\<lambda>r. r=last p_\<alpha>)"
    unfolding last_seg_impl_def
    apply (refine_rcg order_trans[OF seg_set_impl_correct] refine_vcg)
    using assms apply (auto simp add: p_\<alpha>_def last_conv_nth)
    done

end

context fr_graph
begin

  definition "last_seg_impl s \<equiv> GS.last_seg_impl s"
  lemmas last_seg_impl_def_opt = 
    last_seg_impl_def[abs_def, THEN opt_GSdef, 
      unfolded GS.last_seg_impl_def GS.seg_set_impl_def 
    GS.seg_start_def GS.seg_end_def GS_sel_simps] 
    (* TODO: Some potential for optimization here: the assertion 
      guarantees that length B - 1 + 1 = length B !*)

  lemma last_seg_impl_refine: 
    assumes A: "(s,(p,D,pE))\<in>GS_rel"
    assumes NE: "p\<noteq>[]"
    shows "last_seg_impl s \<le> \<Down>Id (RETURN (last p))"
  proof -
    from A have 
      [simp]: "p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s" 
        and INV: "GS_invar s"
      by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)

    show ?thesis
      unfolding last_seg_impl_def[abs_def]
      apply (rule order_trans[OF GS_invar.last_seg_impl_correct])
      using INV NE
      apply (simp_all) 
      done
  qed

  definition compute_SCC_impl :: "'v set list nres" where
    "compute_SCC_impl \<equiv> do {
      stat_start_nres;
      let so = ([],Map.empty);
      (l,D) \<leftarrow> FOREACHi (\<lambda>it (l,s). cscc_outer_invar it (l,oGS_\<alpha> s)) 
        V0 (\<lambda>v0 (l,I0). do {
          if \<not>is_done_oimpl v0 I0 then do {
            let ls = (l,initial_impl v0 I0);

            (l,(S,B,I,P))\<leftarrow>WHILEIT (\<lambda>(l,s). cscc_invar v0 (oGS_\<alpha> I0) (l,GS.\<alpha> s))
              (\<lambda>(l,s). \<not>path_is_empty_impl s) (\<lambda>(l,s).
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,s) \<leftarrow> select_edge_impl s;

              case vo of 
                Some v \<Rightarrow> do {
                  if is_on_stack_impl v s then do {
                    s\<leftarrow>collapse_impl v s;
                    RETURN (l,s)
                  } else if \<not>is_done_impl v s then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    RETURN (l,push_impl v s)
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN (l,s)
                  }
                }
              | None \<Rightarrow> do {
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  scc \<leftarrow> last_seg_impl s;
                  s\<leftarrow>pop_impl s;
                  let l = scc#l;
                  RETURN (l,s)
                }
            }) (ls);
            RETURN (l,I)
          } else RETURN (l,I0)
      }) so;
      stat_stop_nres;
      RETURN l
    }"

  lemma compute_SCC_impl_refine: "compute_SCC_impl \<le> \<Down>Id compute_SCC"
  proof -
    note [refine2] = bind_Let_refine2[OF last_seg_impl_refine]

    have [refine2]: "\<And>s' p D pE l' l v' v. \<lbrakk>
      (s',(p,D,pE))\<in>GS_rel;
      (l',l)\<in>Id;
      (v',v)\<in>Id;
      v\<in>\<Union>(set p)
    \<rbrakk> \<Longrightarrow> do { s'\<leftarrow>collapse_impl v' s'; RETURN (l',s') } 
      \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (RETURN (l,collapse v (p,D,pE)))"
      apply (refine_rcg order_trans[OF collapse_refine] refine_vcg)
      apply assumption+
      apply (auto simp add: pw_le_iff refine_pw_simps)
      done

    note [[goals_limit = 1]]
    show ?thesis
      unfolding compute_SCC_impl_def compute_SCC_def
      apply (refine_rcg
        bind_refine'
        select_edge_refine push_refine 
        pop_refine
        (*collapse_refine*) 
        initial_refine
        oinitial_refine
        (*last_seg_impl_refine*)
        prod_relI IdI
        inj_on_id
      )

      apply refine_dref_type
      apply (vc_solve (nopre) solve: asm_rl I_to_outer
        simp: GS_rel_def br_def GS.\<alpha>_def oGS_rel_def oGS_\<alpha>_def 
        is_on_stack_refine path_is_empty_refine is_done_refine is_done_orefine
      )

      done
  qed

end

end
