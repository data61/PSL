section \<open>Lasso Finding Algorithm for Generalized B\"uchi Graphs \label{sec:gbg}\<close>
theory Gabow_GBG
imports 
  Gabow_Skeleton 
  CAVA_Automata.Lasso
  Find_Path
begin

(* TODO: convenience locale, consider merging this with invariants *)
locale igb_fr_graph = 
  igb_graph G + fr_graph G
  for G :: "('Q,'more) igb_graph_rec_scheme"

lemma igb_fr_graphI:
  assumes "igb_graph G"
  assumes "finite ((g_E G)\<^sup>* `` g_V0 G)"
  shows "igb_fr_graph G"
proof -
  interpret igb_graph G by fact
  show ?thesis using assms(2) by unfold_locales
qed

text \<open>
  We implement an algorithm that computes witnesses for the 
  non-emptiness of Generalized B\"uchi Graphs (GBG).
\<close>

section \<open>Specification\<close>
context igb_graph
begin
  definition ce_correct 
    \<comment> \<open>Specifies a correct counter-example\<close>
    where
    "ce_correct Vr Vl \<equiv> (\<exists>pr pl. 
        Vr \<subseteq> E\<^sup>*``V0 \<and> Vl \<subseteq> E\<^sup>*``V0 \<comment> \<open>Only reachable nodes are covered\<close>
      \<and> set pr\<subseteq>Vr \<and> set pl\<subseteq>Vl     \<comment> \<open>The paths are inside the specified sets\<close>
      \<and> Vl\<times>Vl \<subseteq> (E \<inter> Vl\<times>Vl)\<^sup>*      \<comment> \<open>\<open>Vl\<close> is mutually connected\<close>
      \<and> Vl\<times>Vl \<inter> E \<noteq> {}            \<comment> \<open>\<open>Vl\<close> is non-trivial\<close>
      \<and> is_lasso_prpl (pr,pl))    \<comment> \<open>Paths form a lasso\<close>
    "     

  definition find_ce_spec :: "('Q set \<times> 'Q set) option nres" where
    "find_ce_spec \<equiv> SPEC (\<lambda>r. case r of
      None \<Rightarrow> (\<forall>prpl. \<not>is_lasso_prpl prpl)
    | Some (Vr,Vl) \<Rightarrow> ce_correct Vr Vl
    )"

  definition find_lasso_spec :: "('Q list \<times> 'Q list) option nres" where
    "find_lasso_spec \<equiv> SPEC (\<lambda>r. case r of
      None \<Rightarrow> (\<forall>prpl. \<not>is_lasso_prpl prpl)
    | Some prpl \<Rightarrow> is_lasso_prpl prpl
    )"

end

section \<open>Invariant Extension\<close>

text \<open>Extension of the outer invariant:\<close>
context igb_fr_graph
begin
  definition no_acc_over
    \<comment> \<open>Specifies that there is no accepting cycle touching a set of nodes\<close>
    where
    "no_acc_over D \<equiv> \<not>(\<exists>v\<in>D. \<exists>pl. pl\<noteq>[] \<and> path E v pl v \<and> 
    (\<forall>i<num_acc. \<exists>q\<in>set pl. i\<in>acc q))"

  definition "fgl_outer_invar_ext \<equiv> \<lambda>it (brk,D). 
    case brk of None \<Rightarrow> no_acc_over D | Some (Vr,Vl) \<Rightarrow> ce_correct Vr Vl"

  definition "fgl_outer_invar \<equiv> \<lambda>it (brk,D). case brk of 
    None \<Rightarrow> outer_invar it D \<and> no_acc_over D
  | Some (Vr,Vl) \<Rightarrow> ce_correct Vr Vl"
  
end

text \<open>Extension of the inner invariant:\<close>
locale fgl_invar_loc = 
  invar_loc G v0 D0 p D pE 
  + igb_graph G
  for G :: "('Q, 'more) igb_graph_rec_scheme"
  and v0 D0 and brk :: "('Q set \<times> 'Q set) option" and p D pE +
  assumes no_acc: "brk=None \<Longrightarrow> \<not>(\<exists>v pl. pl\<noteq>[] \<and> path lvE v pl v \<and> 
    (\<forall>i<num_acc. \<exists>q\<in>set pl. i\<in>acc q))" \<comment> \<open>No accepting cycle over 
      visited edges\<close>
  assumes acc: "brk=Some (Vr,Vl) \<Longrightarrow> ce_correct Vr Vl"
begin
  lemma locale_this: "fgl_invar_loc G v0 D0 brk p D pE"
    by unfold_locales
  lemma invar_loc_this: "invar_loc G v0 D0 p D pE" by unfold_locales
  lemma eas_gba_graph_this: "igb_graph G" by unfold_locales
end

definition (in igb_graph) "fgl_invar v0 D0 \<equiv> 
  \<lambda>(brk, p, D, pE). fgl_invar_loc G v0 D0 brk p D pE"

section \<open>Definition of the Lasso-Finding Algorithm\<close>

context igb_fr_graph
begin
  definition find_ce :: "('Q set \<times> 'Q set) option nres" where
    "find_ce \<equiv> do {
      let D = {};
      (brk,_)\<leftarrow>FOREACHci fgl_outer_invar V0 
        (\<lambda>(brk,_). brk=None) 
        (\<lambda>v0 (brk,D0). do {
          if v0\<notin>D0 then do {
            let s = (None,initial v0 D0);

            (brk,p,D,pE) \<leftarrow> WHILEIT (fgl_invar v0 D0)
              (\<lambda>(brk,p,D,pE). brk=None \<and> p \<noteq> []) (\<lambda>(_,p,D,pE). 
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,(p,D,pE)) \<leftarrow> select_edge (p,D,pE);

              ASSERT (p\<noteq>[]);
              case vo of 
                Some v \<Rightarrow> do {
                  if v \<in> \<Union>(set p) then do {
                    \<comment> \<open>Collapse\<close>
                    let (p,D,pE) = collapse v (p,D,pE);

                    ASSERT (p\<noteq>[]);

                    if \<forall>i<num_acc. \<exists>q\<in>last p. i\<in>acc q then
                      RETURN (Some (\<Union>(set (butlast p)),last p),p,D,pE)
                    else
                      RETURN (None,p,D,pE)
                  } else if v\<notin>D then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    RETURN (None,push v (p,D,pE))
                  } else RETURN (None,p,D,pE)
                }
              | None \<Rightarrow> do {
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  ASSERT (pE \<inter> last p \<times> UNIV = {});
                  RETURN (None,pop (p,D,pE))
                }
            }) s;
            ASSERT (brk=None \<longrightarrow> (p=[] \<and> pE={}));
            RETURN (brk,D)
          } else 
            RETURN (brk,D0)
      }) (None,D);
      RETURN brk
    }"
end

section \<open>Invariant Preservation\<close>


context igb_fr_graph
begin

  definition "fgl_invar_part \<equiv> \<lambda>(brk, p, D, pE). 
    fgl_invar_loc_axioms G brk p D pE"

  lemma fgl_outer_invarI[intro?]:
    "\<lbrakk>
      brk=None \<Longrightarrow> outer_invar it D; 
      \<lbrakk>brk=None \<Longrightarrow> outer_invar it D\<rbrakk> \<Longrightarrow> fgl_outer_invar_ext it (brk,D)\<rbrakk> 
      \<Longrightarrow> fgl_outer_invar it (brk,D)"
    unfolding outer_invar_def fgl_outer_invar_ext_def fgl_outer_invar_def
    apply (auto split: prod.splits option.splits)
    done

  lemma fgl_invarI[intro?]:
    "\<lbrakk> invar v0 D0 PDPE; 
       invar v0 D0 PDPE \<Longrightarrow> fgl_invar_part (B,PDPE)\<rbrakk> 
     \<Longrightarrow> fgl_invar v0 D0 (B,PDPE)"
    unfolding invar_def fgl_invar_part_def fgl_invar_def
    apply (simp split: prod.split_asm)
    apply intro_locales
    apply (simp add: invar_loc_def)
    apply assumption
    done


  lemma fgl_invar_initial: 
    assumes OINV: "fgl_outer_invar it (None,D0)"
    assumes A: "v0\<in>it" "v0\<notin>D0"
    shows "fgl_invar_part (None, initial v0 D0)"
  proof -
    from OINV interpret outer_invar_loc G it D0 
      by (simp add: fgl_outer_invar_def outer_invar_def)

    from OINV have no_acc: "no_acc_over D0"
      by (simp add: fgl_outer_invar_def fgl_outer_invar_ext_def)

    {
      fix v pl

      assume "pl \<noteq> []" and P: "path (vE [{v0}] D0 (E \<inter> {v0} \<times> UNIV)) v pl v"
      hence 1: "v\<in>D0"
        by (cases pl) (auto simp: path_cons_conv vE_def touched_def)
      have 2: "path E v pl v" using path_mono[OF vE_ss_E P] .
      note 1 2
    } note AUX1=this


    show ?thesis
      unfolding fgl_invar_part_def
      apply (simp split: prod.splits add: initial_def)
      apply unfold_locales
      using \<open>v0\<notin>D0\<close>
      using AUX1 no_acc unfolding no_acc_over_def apply blast
      by simp
  qed

  lemma fgl_invar_pop:
    assumes INV: "fgl_invar v0 D0 (None,p,D,pE)"
    assumes INV': "invar v0 D0 (pop (p,D,pE))"
    assumes NE[simp]: "p\<noteq>[]"
    assumes NO': "pE \<inter> last p \<times> UNIV = {}"
    shows "fgl_invar_part (None, pop (p,D,pE))"
  proof -
    from INV interpret fgl_invar_loc G v0 D0 None p D pE 
      by (simp add: fgl_invar_def)

    show ?thesis
      apply (unfold fgl_invar_part_def pop_def)
      apply (simp split: prod.splits)
      apply unfold_locales
      unfolding vE_pop[OF NE]

      using no_acc apply auto []
      apply simp
      done
  qed

  lemma fgl_invar_collapse_ce_aux:
    assumes INV: "invar v0 D0 (p, D, pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes NONTRIV: "vE p D pE \<inter> (last p \<times> last p) \<noteq> {}"
    assumes ACC: "\<forall>i<num_acc. \<exists>q\<in>last p. i\<in>acc q"
    shows "fgl_invar_part (Some (\<Union>(set (butlast p)), last p), p, D, pE)"
  proof -
    from INV interpret invar_loc G v0 D0 p D pE by (simp add: invar_def)
    txt \<open>The last collapsed node on the path contains states from all 
      accepting sets.
      As it is strongly connected and reachable, we get a counter-example. 
      Here, we explicitely construct the lasso.\<close>

    let ?Er = "E \<inter> (\<Union>(set (butlast p)) \<times> UNIV)"

    txt \<open>We choose a node in the last Cnode, that is reachable only using
      former Cnodes.\<close>

    obtain w where "(v0,w)\<in>?Er\<^sup>*" "w\<in>last p"
    proof cases
      assume "length p = 1"
      hence "v0\<in>last p"
        using root_v0 
        by (cases p) auto
      thus thesis by (auto intro: that)
    next
      assume "length p\<noteq>1"
      hence "length p > 1" by (cases p) auto
      hence "Suc (length p - 2) < length p" by auto
      from p_connected'[OF this] obtain u v where
        UIP: "u\<in>p!(length p - 2)" and VIP: "v\<in>p!(length p - 1)" and "(u,v)\<in>lvE"
        using \<open>length p > 1\<close> by auto
      from root_v0 have V0IP: "v0\<in>p!0" by (cases p) auto
      
      from VIP have "v\<in>last p" by (cases p rule: rev_cases) auto

      from pathI[OF V0IP UIP] \<open>length p > 1\<close> have 
        "(v0,u)\<in>(lvE \<inter> \<Union>(set (butlast p)) \<times> \<Union>(set (butlast p)))\<^sup>*"
        (is "_ \<in> \<dots>\<^sup>*")  
        by (simp add: path_seg_butlast)
      also have "\<dots> \<subseteq> ?Er" using lvE_ss_E by auto
      finally (rtrancl_mono_mp[rotated]) have "(v0,u)\<in>?Er\<^sup>*" .
      also note \<open>(u,v)\<in>lvE\<close> UIP hence "(u,v)\<in>?Er" using lvE_ss_E \<open>length p > 1\<close> 
        apply (auto simp: Bex_def in_set_conv_nth)
        by (metis One_nat_def Suc_lessE \<open>Suc (length p - 2) < length p\<close> 
          diff_Suc_1 length_butlast nth_butlast)
      finally show ?thesis by (rule that) fact 
    qed
    then obtain "pr" where 
      P_REACH: "path E v0 pr w" and 
      R_SS: "set pr \<subseteq> \<Union>(set (butlast p))"
      apply -
      apply (erule rtrancl_is_path)
      apply (frule path_nodes_edges)
      apply (auto 
        dest!: order_trans[OF _ image_Int_subset] 
        dest: path_mono[of _ E, rotated])
      done

    have [simp]: "last p = p!(length p - 1)" by (cases p rule: rev_cases) auto

    txt \<open>From that node, we construct a lasso by inductively appending a path
      for each accepting set\<close>
    {
      fix na
      assume na_def: "na = num_acc"

      have "\<exists>pl. pl\<noteq>[] 
        \<and> path (lvE \<inter> last p\<times>last p) w pl w 
        \<and> (\<forall>i<num_acc. \<exists>q\<in>set pl. i\<in>acc q)"
        using ACC
        unfolding na_def[symmetric]
      proof (induction na)
        case 0 

        from NONTRIV obtain u v 
          where "(u,v)\<in>lvE \<inter> last p \<times> last p" "u\<in>last p" "v\<in>last p"
          by auto
        from cnode_connectedI \<open>w\<in>last p\<close> \<open>u\<in>last p\<close> 
        have "(w,u)\<in>(lvE \<inter> last p \<times> last p)\<^sup>*"
          by auto
        also note \<open>(u,v)\<in>lvE \<inter> last p \<times> last p\<close>
        also (rtrancl_into_trancl1) from cnode_connectedI \<open>v\<in>last p\<close> \<open>w\<in>last p\<close> 
        have "(v,w)\<in>(lvE \<inter> last p \<times> last p)\<^sup>*"
          by auto
        finally obtain pl where "pl\<noteq>[]" "path (lvE \<inter> last p \<times> last p) w pl w"
          by (rule trancl_is_path)
        thus ?case by auto
      next
        case (Suc n)
        from Suc.prems have "\<forall>i<n. \<exists>q\<in>last p. i\<in>acc q" by auto
        with Suc.IH obtain pl where IH: 
          "pl\<noteq>[]" 
          "path (lvE \<inter> last p \<times> last p) w pl w" 
          "\<forall>i<n. \<exists>q\<in>set pl. i\<in>acc q" 
          by blast
  
        from Suc.prems obtain v where "v\<in>last p" and "n\<in>acc v" by auto
        from cnode_connectedI \<open>w\<in>last p\<close> \<open>v\<in>last p\<close> 
        have "(w,v)\<in>(lvE \<inter> last p \<times> last p)\<^sup>*" by auto
        then obtain pl1 where P1: "path (lvE \<inter> last p \<times> last p) w pl1 v" 
          by (rule rtrancl_is_path)
        also from cnode_connectedI \<open>w\<in>last p\<close> \<open>v\<in>last p\<close> 
        have "(v,w)\<in>(lvE \<inter> last p \<times> last p)\<^sup>*" by auto
        then obtain pl2 where P2: "path (lvE \<inter> last p \<times> last p) v pl2 w"
          by (rule rtrancl_is_path)
        also (path_conc) note IH(2)
        finally (path_conc) have 
          P: "path (lvE \<inter> last p \<times> last p) w (pl1@pl2@pl) w"
          by simp
        moreover from IH(1) have "pl1@pl2@pl \<noteq> []" by simp
        moreover have "\<forall>i'<n. \<exists>q\<in>set (pl1@pl2@pl). i'\<in>acc q" using IH(3) by auto
        moreover have "v\<in>set (pl1@pl2@pl)" using P1 P2 P IH(1)
          apply (cases pl2, simp_all add: path_cons_conv path_conc_conv)
          apply (cases pl, simp_all add: path_cons_conv)
          apply (cases pl1, simp_all add: path_cons_conv)
          done
        with \<open>n\<in>acc v\<close> have "\<exists>q\<in>set (pl1@pl2@pl). n\<in>acc q" by auto
        ultimately show ?case
          apply (intro exI conjI)
          apply assumption+
          apply (auto elim: less_SucE)
          done
      qed
    }
    then obtain pl where pl: "pl\<noteq>[]" "path (lvE \<inter> last p\<times>last p) w pl w" 
      "\<forall>i<num_acc. \<exists>q\<in>set pl. i\<in>acc q" by blast
    hence "path E w pl w" and L_SS: "set pl \<subseteq> last p"
      apply -
      apply (frule path_mono[of _ E, rotated])
      using lvE_ss_E
      apply auto [2]

      apply (drule path_nodes_edges)
      apply (drule order_trans[OF _ image_Int_subset])
      apply auto []
      done

    have LASSO: "is_lasso_prpl (pr,pl)"
      unfolding is_lasso_prpl_def is_lasso_prpl_pre_def
      using \<open>path E w pl w\<close> P_REACH pl by auto
    
    from p_sc have "last p \<times> last p \<subseteq> (lvE \<inter> last p \<times> last p)\<^sup>*" by auto
    with lvE_ss_E have VL_CLOSED: "last p \<times> last p \<subseteq> (E \<inter> last p \<times> last p)\<^sup>*"
      apply (erule_tac order_trans)
      apply (rule rtrancl_mono)
      by blast

    have NONTRIV': "last p \<times> last p \<inter> E \<noteq> {}"
      by (metis Int_commute NONTRIV disjoint_mono lvE_ss_E subset_refl)

    from order_trans[OF path_touched touched_reachable]
    have LP_REACH: "last p \<subseteq> E\<^sup>*``V0" 
      and BLP_REACH: "\<Union>(set (butlast p)) \<subseteq> E\<^sup>*``V0"
      apply -
      apply (cases p rule: rev_cases)
      apply simp
      apply auto []

      apply (cases p rule: rev_cases)
      apply simp
      apply auto []
      done
      
    show ?thesis
      apply (simp add: fgl_invar_part_def)
      apply unfold_locales
      apply simp

      using LASSO R_SS L_SS VL_CLOSED NONTRIV' LP_REACH BLP_REACH
      unfolding ce_correct_def 
      apply simp 
      apply blast
      done

  qed

  lemma fgl_invar_collapse_ce:
    fixes u v
    assumes INV: "fgl_invar v0 D0 (None,p,D,pE)"
    defines "pE' \<equiv> pE - {(u,v)}"
    assumes CFMT: "(p',D',pE'') = collapse v (p,D,pE')"
    assumes INV': "invar v0 D0 (p',D',pE'')"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and "u\<in>last p"
    assumes BACK: "v\<in>\<Union>(set p)"
    assumes ACC: "\<forall>i<num_acc. \<exists>q\<in>last p'. i\<in>acc q"
    defines i_def: "i \<equiv> idx_of p v"
    shows "fgl_invar_part (
      Some (\<Union>(set (butlast p')), last p'), 
      collapse v (p,D,pE'))"
  proof -

    from CFMT have p'_def: "p' = collapse_aux p i" and [simp]: "D'=D" "pE''=pE'"
      by (simp_all add: collapse_def i_def)

    from INV interpret fgl_invar_loc G v0 D0 None p D pE 
      by (simp add: fgl_invar_def)

    from idx_of_props[OF BACK] have "i<length p" and "v\<in>p!i" 
      by (simp_all add: i_def)

    have "u\<in>last p'" 
      using \<open>u\<in>last p\<close> \<open>i<length p\<close> 
      unfolding p'_def collapse_aux_def
      apply (simp add: last_drop last_snoc)
      by (metis Misc.last_in_set drop_eq_Nil last_drop not_le)
    moreover have "v\<in>last p'" 
      using \<open>v\<in>p!i\<close> \<open>i<length p\<close> 
      unfolding p'_def collapse_aux_def
      by (metis UnionI append_Nil Cons_nth_drop_Suc in_set_conv_decomp last_snoc)
    ultimately have "vE p' D pE' \<inter> last p' \<times> last p' \<noteq> {}" 
      unfolding p'_def pE'_def by (auto simp: E)
    
    have "p'\<noteq>[]" by (simp add: p'_def collapse_aux_def)

    have [simp]: "collapse v (p,D,pE') = (p',D,pE')" 
      unfolding collapse_def p'_def i_def
      by simp

    show ?thesis
      apply simp
      apply (rule fgl_invar_collapse_ce_aux) 
      using INV' apply simp
      apply fact+
      done
  qed

  lemma fgl_invar_collapse_nce:
    fixes u v
    assumes INV: "fgl_invar v0 D0 (None,p,D,pE)"
    defines "pE' \<equiv> pE - {(u,v)}"
    assumes CFMT: "(p',D',pE'') = collapse v (p,D,pE')"
    assumes INV': "invar v0 D0 (p',D',pE'')"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and "u\<in>last p"
    assumes BACK: "v\<in>\<Union>(set p)"
    assumes NACC: "j<num_acc" "\<forall>q\<in>last p'. j\<notin>acc q"
    defines "i \<equiv> idx_of p v"
    shows "fgl_invar_part (None, collapse v (p,D,pE'))"
  proof -
    from CFMT have p'_def: "p' = collapse_aux p i" and [simp]: "D'=D" "pE''=pE'"
      by (simp_all add: collapse_def i_def)

    have [simp]: "collapse v (p,D,pE') = (p',D,pE')" 
      by (simp add: collapse_def p'_def i_def)

    from INV interpret fgl_invar_loc G v0 D0 None p D pE 
      by (simp add: fgl_invar_def)

    from INV' interpret inv': invar_loc G v0 D0 p' D pE' by (simp add: invar_def)

    define vE' where "vE' = vE p' D pE'"

    have vE'_alt: "vE' = insert (u,v) lvE"
      by (simp add: vE'_def p'_def pE'_def E)

    from idx_of_props[OF BACK] have "i<length p" and "v\<in>p!i" 
      by (simp_all add: i_def)

    have "u\<in>last p'" 
      using \<open>u\<in>last p\<close> \<open>i<length p\<close>
      unfolding p'_def collapse_aux_def
      apply (simp add: last_drop last_snoc)
      by (metis Misc.last_in_set drop_eq_Nil last_drop leD)
    moreover have "v\<in>last p'" 
      using \<open>v\<in>p!i\<close> \<open>i<length p\<close> 
      unfolding p'_def collapse_aux_def
      by (metis UnionI append_Nil Cons_nth_drop_Suc in_set_conv_decomp last_snoc)
    ultimately have "vE' \<inter> last p' \<times> last p' \<noteq> {}" 
      unfolding vE'_alt by (auto)
    
    have "p'\<noteq>[]" by (simp add: p'_def collapse_aux_def)

    {
      txt \<open>
        We show that no visited strongly connected component contains states
        from all acceptance sets.\<close>
      fix w pl
      txt \<open>For this, we chose a non-trivial loop inside the visited edges\<close>
      assume P: "path vE' w pl w" and NT: "pl\<noteq>[]"
      txt \<open>And show that there is one acceptance set disjoint with the nodes
        of the loop\<close>
      have "\<exists>i<num_acc. \<forall>q\<in>set pl. i\<notin>acc q"
      proof cases
        assume "set pl \<inter> last p' = {}" 
          \<comment> \<open>Case: The loop is outside the last Cnode\<close>
        with path_restrict[OF P] \<open>u\<in>last p'\<close> \<open>v\<in>last p'\<close> have "path lvE w pl w"
          apply -
          apply (drule path_mono[of _ lvE, rotated])
          unfolding vE'_alt
          by auto
        with no_acc NT show ?thesis by auto
      next
        assume "set pl \<inter> last p' \<noteq> {}" 
          \<comment> \<open>Case: The loop touches the last Cnode\<close>
        txt \<open>Then, the loop must be completely inside the last CNode\<close>
        from inv'.loop_in_lastnode[folded vE'_def, OF P \<open>p'\<noteq>[]\<close> this] 
        have "w\<in>last p'" "set pl \<subseteq> last p'" .
        with NACC show ?thesis by blast
      qed
    } note AUX_no_acc = this

    show ?thesis
      apply (simp add: fgl_invar_part_def)
      apply unfold_locales
      using AUX_no_acc[unfolded vE'_def] apply auto []
      
      apply simp
      done
  qed

  lemma collapse_ne: "([],D',pE') \<noteq> collapse v (p,D,pE)"
    by (simp add: collapse_def collapse_aux_def Let_def)

  lemma fgl_invar_push:
    assumes INV: "fgl_invar v0 D0 (None,p,D,pE)"
    assumes BRK[simp]: "brk=None" 
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and UIL: "u\<in>last p"
    assumes VNE: "v\<notin>\<Union>(set p)" "v\<notin>D"
    assumes INV': "invar v0 D0 (push v (p,D,pE - {(u,v)}))"
    shows "fgl_invar_part (None, push v (p,D,pE - {(u,v)}))"
  proof -
    from INV interpret fgl_invar_loc G v0 D0 None p D pE 
      by (simp add: fgl_invar_def)

    define pE' where "pE' = (pE - {(u,v)} \<union> E\<inter>{v}\<times>UNIV)"

    have [simp]: "push v (p,D,pE - {(u,v)}) = (p@[{v}],D,pE')"
      by (simp add: push_def pE'_def)

    from INV' interpret inv': invar_loc G v0 D0 "(p@[{v}])" D "pE'"
      by (simp add: invar_def)

    note defs_fold = vE_push[OF E UIL VNE, folded pE'_def]

    {
      txt \<open>We show that there still is no loop that contains all accepting
        nodes. For this, we choose some loop.\<close>
      fix w pl
      assume P: "path (insert (u,v) lvE) w pl w" and [simp]: "pl\<noteq>[]"
      have "\<exists>i<num_acc. \<forall>q\<in>set pl. i\<notin>acc q" 
      proof cases
        assume "v\<in>set pl" \<comment> \<open>Case: The newly pushed last cnode is on the loop\<close>
        txt \<open>Then the loop is entirely on the last cnode\<close>
        with inv'.loop_in_lastnode[unfolded defs_fold, OF P]
        have [simp]: "w=v" and SPL: "set pl = {v}" by auto
        txt \<open>However, we then either have that the last cnode is contained in
          the last but one cnode, or that there is a visited edge inside the
          last cnode.\<close>
        from P SPL have "u=v \<or> (v,v)\<in>lvE" 
          apply (cases pl) apply (auto simp: path_cons_conv)
          apply (case_tac list)
          apply (auto simp: path_cons_conv)
          done
        txt \<open>Both leads to a contradiction\<close>
        hence False proof
          assume "u=v" \<comment> \<open>This is impossible, as @{text "u"} was on the 
            original path, but @{text "v"} was not\<close>
          with UIL VNE show False by auto
        next
          assume "(v,v)\<in>lvE" \<comment> \<open>This is impossible, as all visited edges are
            from touched nodes, but @{text "v"} was untouched\<close>
          with vE_touched VNE show False unfolding touched_def by auto
        qed
        thus ?thesis ..
      next
        assume A: "v\<notin>set pl" 
          \<comment> \<open>Case: The newly pushed last cnode is not on the loop\<close>
        txt \<open>Then, the path lays inside the old visited edges\<close>
        have "path lvE w pl w" 
        proof -
          have "w\<in>set pl" using P by (cases pl) (auto simp: path_cons_conv)
          with A show ?thesis using path_restrict[OF P]
            apply -
            apply (drule path_mono[of _ lvE, rotated])
            apply (cases pl, auto) []
            
            apply assumption
            done
        qed
        txt \<open>And thus, the proposition follows from the invariant on the old
          state\<close>
        with no_acc show ?thesis 
          apply simp
          using \<open>pl\<noteq>[]\<close> 
          by blast
      qed
    } note AUX_no_acc = this

    show ?thesis
      unfolding fgl_invar_part_def
      apply simp
      apply unfold_locales
      unfolding defs_fold

      using AUX_no_acc apply auto []
      
      apply simp
      done
  qed


  lemma fgl_invar_skip:
    assumes INV: "fgl_invar v0 D0 (None,p,D,pE)"
    assumes BRK[simp]: "brk=None" 
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and UIL: "u\<in>last p"
    assumes VID: "v\<in>D"
    assumes INV': "invar v0 D0 (p, D, (pE - {(u,v)}))"
    shows "fgl_invar_part (None, p, D, (pE - {(u,v)}))"
  proof -
    from INV interpret fgl_invar_loc G v0 D0 None p D pE 
      by (simp add: fgl_invar_def)
    from INV' interpret inv': invar_loc G v0 D0 p D "(pE - {(u,v)})" 
      by (simp add: invar_def)

    {
      txt \<open>We show that there still is no loop that contains all accepting
        nodes. For this, we choose some loop.\<close>
      fix w pl
      assume P: "path (insert (u,v) lvE) w pl w" and [simp]: "pl\<noteq>[]"
      from P have "\<exists>i<num_acc. \<forall>q\<in>set pl. i\<notin>acc q" 
      proof (cases rule: path_edge_rev_cases)
        case no_use \<comment> \<open>Case: The loop does not use the new edge\<close>
        txt \<open>The proposition follows from the invariant for the old state\<close>
        with no_acc show ?thesis 
          apply simp
          using \<open>pl\<noteq>[]\<close> 
          by blast
      next
        case (split p1 p2) \<comment> \<open>Case: The loop uses the new edge\<close>
        txt \<open>As done is closed under transitions, the nodes of the edge have
          already been visited\<close>
        from split(2) D_closed_vE_rtrancl 
        have WID: "w\<in>D" 
          using VID by (auto dest!: path_is_rtrancl)
        from split(1) WID D_closed_vE_rtrancl have "u\<in>D"
          apply (cases rule: path_edge_cases)
          apply (auto dest!: path_is_rtrancl)
          done
        txt \<open>Which is a contradition to the assumptions\<close>
        with UIL p_not_D have False by (cases p rule: rev_cases) auto
        thus ?thesis ..
      qed
    } note AUX_no_acc = this


    show ?thesis 
      apply (simp add: fgl_invar_part_def)
      apply unfold_locales
      unfolding vE_remove[OF NE E]

      using AUX_no_acc apply auto []

      apply simp
      done

  qed

  lemma fgl_outer_invar_initial: 
    "outer_invar V0 {} \<Longrightarrow> fgl_outer_invar_ext V0 (None, {})"
    unfolding fgl_outer_invar_ext_def
    apply (simp add: no_acc_over_def)
    done

  lemma fgl_outer_invar_brk:
    assumes INV: "fgl_invar v0 D0 (Some (Vr,Vl),p,D,pE)"
    shows "fgl_outer_invar_ext anyIt (Some (Vr,Vl), anyD)"
  proof -
    from INV interpret fgl_invar_loc G v0 D0 "Some (Vr,Vl)" p D pE
      by (simp add: fgl_invar_def)

    from acc show ?thesis by (simp add: fgl_outer_invar_ext_def)
  qed

  lemma fgl_outer_invar_newnode_nobrk:
    assumes A: "v0\<notin>D0" "v0\<in>it" 
    assumes OINV: "fgl_outer_invar it (None,D0)"
    assumes INV: "fgl_invar v0 D0 (None,[],D',pE)"
    shows "fgl_outer_invar_ext (it-{v0}) (None,D')"
  proof -
    from OINV interpret outer_invar_loc G it D0 
      unfolding fgl_outer_invar_def outer_invar_def by simp

    from INV interpret inv: fgl_invar_loc G v0 D0 None "[]" D' pE 
      unfolding fgl_invar_def by simp

    from inv.pE_fin have [simp]: "pE = {}" by simp

    { fix v pl
      assume A: "v\<in>D'" "path E v pl v"
      have "path (E \<inter> D' \<times> UNIV) v pl v"
        apply (rule path_mono[OF _ path_restrict_closed[OF inv.D_closed A]])
        by auto
    } note AUX1=this

    show ?thesis
      unfolding fgl_outer_invar_ext_def
      apply simp
      using inv.no_acc AUX1 
      apply (auto simp add: vE_def touched_def no_acc_over_def) []
      done
  qed

  lemma fgl_outer_invar_newnode:
    assumes A: "v0\<notin>D0" "v0\<in>it" 
    assumes OINV: "fgl_outer_invar it (None,D0)"
    assumes INV: "fgl_invar v0 D0 (brk,p,D',pE)"
    assumes CASES: "(\<exists>Vr Vl. brk = Some (Vr, Vl)) \<or> p = []"
    shows "fgl_outer_invar_ext (it-{v0}) (brk,D')"
    using CASES
    apply (elim disjE1)
    using fgl_outer_invar_brk[of v0 D0 _ _ p D' pE] INV 
    apply - 
    apply (auto, assumption) []
    using fgl_outer_invar_newnode_nobrk[OF A] OINV INV apply auto []
    done

  lemma fgl_outer_invar_Dnode:
    assumes "fgl_outer_invar it (None, D)" "v\<in>D"
    shows "fgl_outer_invar_ext (it - {v}) (None, D)"
    using assms
    by (auto simp: fgl_outer_invar_def fgl_outer_invar_ext_def)

  
  lemma fgl_fin_no_lasso:
    assumes A: "fgl_outer_invar {} (None, D)"
    assumes B: "is_lasso_prpl prpl"
    shows "False"
  proof -
    obtain "pr" pl where [simp]: "prpl = (pr,pl)" by (cases prpl)
    from A have NA: "no_acc_over D" 
      by (simp add: fgl_outer_invar_def fgl_outer_invar_ext_def)

    from A have "outer_invar {} D" by (simp add: fgl_outer_invar_def)
    with fin_outer_D_is_reachable have [simp]: "D=E\<^sup>*``V0" by simp

    from NA B show False
      apply (simp add: no_acc_over_def is_lasso_prpl_def is_lasso_prpl_pre_def)
      apply clarsimp
      apply (blast dest: path_is_rtrancl)
      done
  qed

  lemma fgl_fin_lasso:
    assumes A: "fgl_outer_invar it (Some (Vr,Vl), D)"
    shows "ce_correct Vr Vl"
    using A by (simp add: fgl_outer_invar_def fgl_outer_invar_ext_def)


  lemmas fgl_invar_preserve = 
    fgl_invar_initial fgl_invar_push fgl_invar_pop 
    fgl_invar_collapse_ce fgl_invar_collapse_nce fgl_invar_skip
    fgl_outer_invar_newnode fgl_outer_invar_Dnode
    invar_initial outer_invar_initial fgl_invar_initial fgl_outer_invar_initial
    fgl_fin_no_lasso fgl_fin_lasso

end

section \<open>Main Correctness Proof\<close>

context igb_fr_graph
begin
  lemma outer_invar_from_fgl_invarI: 
    "fgl_outer_invar it (None,D) \<Longrightarrow> outer_invar it D"
    unfolding fgl_outer_invar_def outer_invar_def
    by (simp split: prod.splits)

  lemma invar_from_fgl_invarI: "fgl_invar v0 D0 (B,PDPE) \<Longrightarrow> invar v0 D0 PDPE"
    unfolding fgl_invar_def invar_def
    apply (simp split: prod.splits)
    unfolding fgl_invar_loc_def by simp
   
  theorem find_ce_correct: "find_ce \<le> find_ce_spec"
  proof -
    note [simp del] = Union_iff

    show ?thesis
      unfolding find_ce_def find_ce_spec_def select_edge_def select_def
      apply (refine_rcg
        WHILEIT_rule[where R="inv_image (abs_wf_rel v0) snd" for v0]
        refine_vcg 
      )
      
      using [[goals_limit = 5]]

      apply (vc_solve
        rec: fgl_invarI fgl_outer_invarI
        intro: invar_from_fgl_invarI outer_invar_from_fgl_invarI
        dest!: sym[of "collapse a b" for a b]
        simp: collapse_ne
        simp: pE_fin'[OF invar_from_fgl_invarI] finite_V0
        solve: invar_preserve 
        solve: asm_rl[of "_ \<inter> _ = {}"]
        solve: fgl_invar_preserve)
      done
  qed
end

section "Emptiness Check"
text \<open>Using the lasso-finding algorithm, we can define an emptiness check\<close>

context igb_fr_graph
begin
  definition "abs_is_empty \<equiv> do {
    ce \<leftarrow> find_ce;
    RETURN (ce = None)
    }"

  theorem abs_is_empty_correct: 
    "abs_is_empty \<le> SPEC (\<lambda>res. res \<longleftrightarrow> (\<forall>r. \<not>is_acc_run r))"
    unfolding abs_is_empty_def
    apply (refine_rcg refine_vcg 
      order_trans[OF find_ce_correct, unfolded find_ce_spec_def])
    unfolding ce_correct_def
    using lasso_accepted accepted_lasso
    apply (clarsimp split: option.splits)
    apply (metis is_lasso_prpl_of_lasso surj_pair)
    by (metis is_lasso_prpl_conv)

  definition "abs_is_empty_ce \<equiv> do {
    ce \<leftarrow> find_ce;
    case ce of
      None \<Rightarrow> RETURN None
    | Some (Vr,Vl) \<Rightarrow> do {
        ASSERT (\<exists>pr pl. set pr \<subseteq> Vr \<and> set pl \<subseteq> Vl \<and> Vl \<times> Vl \<subseteq> (E \<inter> Vl\<times>Vl)\<^sup>* 
          \<and> is_lasso_prpl (pr,pl));
        (pr,pl) \<leftarrow> SPEC (\<lambda>(pr,pl). 
           set pr \<subseteq> Vr 
          \<and> set pl \<subseteq> Vl 
          \<and> Vl \<times> Vl \<subseteq> (E \<inter> Vl\<times>Vl)\<^sup>*
          \<and> is_lasso_prpl (pr,pl));
        RETURN (Some (pr,pl))
      }
    }"

  theorem abs_is_empty_ce_correct: "abs_is_empty_ce \<le> SPEC (\<lambda>res. case res of
      None \<Rightarrow> (\<forall>r. \<not>is_acc_run r)
    | Some (pr,pl) \<Rightarrow> is_acc_run (pr\<frown>pl\<^sup>\<omega>)
    )"
    unfolding abs_is_empty_ce_def
    apply (refine_rcg refine_vcg 
      order_trans[OF find_ce_correct, unfolded find_ce_spec_def])

    apply (clarsimp_all simp: ce_correct_def)

    using accepted_lasso finite_reachableE_V0 apply (metis is_lasso_prpl_of_lasso surj_pair)
    apply blast
    apply (simp add: lasso_prpl_acc_run)
    done

end

section \<open>Refinement\<close>
text \<open>
  In this section, we refine the lasso finding algorithm to use efficient
  data structures. First, we explicitely keep track of the set of acceptance
  classes for every c-node on the path. Second, we use Gabow's data structure
  to represent the path.
\<close>

subsection \<open>Addition of Explicit Accepting Sets\<close>
text \<open>In a first step, we explicitely keep track of the current set of
  acceptance classes for every c-node on the path.\<close>

type_synonym 'a abs_gstate = "nat set list \<times> 'a abs_state"
type_synonym 'a ce = "('a set \<times> 'a set) option"
type_synonym 'a abs_gostate = "'a ce \<times> 'a set"

context igb_fr_graph
begin

  definition gstate_invar :: "'Q abs_gstate \<Rightarrow> bool" where 
    "gstate_invar \<equiv> \<lambda>(a,p,D,pE). a = map (\<lambda>V. \<Union>(acc`V)) p"

  definition "gstate_rel \<equiv> br snd gstate_invar"

  lemma gstate_rel_sv[relator_props,simp,intro!]: "single_valued gstate_rel"
    by (simp add: gstate_rel_def)

  definition (in -) gcollapse_aux 
    :: "nat set list \<Rightarrow> 'a set list \<Rightarrow> nat \<Rightarrow> nat set list \<times> 'a set list"
    where "gcollapse_aux a p i \<equiv> 
      (take i a @ [\<Union>(set (drop i a))],take i p @ [\<Union>(set (drop i p))])"

  definition (in -) gcollapse :: "'a \<Rightarrow> 'a abs_gstate \<Rightarrow> 'a abs_gstate" 
    where "gcollapse v APDPE \<equiv> 
    let 
      (a,p,D,pE)=APDPE; 
      i=idx_of p v;
      (a,p) = gcollapse_aux a p i
    in (a,p,D,pE)"

  definition "gpush v s \<equiv> 
    let
      (a,s) = s
    in
      (a@[acc v],push v s)"

  definition "gpop s \<equiv>
    let (a,s) = s in (butlast a,pop s)"

  definition ginitial :: "'Q \<Rightarrow> 'Q abs_gostate \<Rightarrow> 'Q abs_gstate" 
    where "ginitial v0 s0 \<equiv> ([acc v0], initial v0 (snd s0))"

  definition goinitial :: "'Q abs_gostate" where "goinitial \<equiv> (None,{})"
  definition go_is_no_brk :: "'Q abs_gostate \<Rightarrow> bool" 
    where "go_is_no_brk s \<equiv> fst s = None"
  definition goD :: "'Q abs_gostate \<Rightarrow> 'Q set" where "goD s \<equiv> snd s"
  definition goBrk :: "'Q abs_gostate \<Rightarrow> 'Q ce" where "goBrk s \<equiv> fst s"
  definition gto_outer :: "'Q ce \<Rightarrow> 'Q abs_gstate \<Rightarrow> 'Q abs_gostate" 
    where "gto_outer brk s \<equiv> let (A,p,D,pE)=s in (brk,D)"

  definition "gselect_edge s \<equiv> do {
    let (a,s)=s; 
    (r,s)\<leftarrow>select_edge s;
    RETURN (r,a,s) 
  }"

  definition gfind_ce :: "('Q set \<times> 'Q set) option nres" where
    "gfind_ce \<equiv> do {
      let os = goinitial;
      os\<leftarrow>FOREACHci fgl_outer_invar V0 (go_is_no_brk) (\<lambda>v0 s0. do {
        if v0\<notin>goD s0 then do {
          let s = (None,ginitial v0 s0);

          (brk,a,p,D,pE) \<leftarrow> WHILEIT (\<lambda>(brk,a,s). fgl_invar v0 (goD s0) (brk,s))
            (\<lambda>(brk,a,p,D,pE). brk=None \<and> p \<noteq> []) (\<lambda>(_,a,p,D,pE). 
          do {
            \<comment> \<open>Select edge from end of path\<close>
            (vo,(a,p,D,pE)) \<leftarrow> gselect_edge (a,p,D,pE);

            ASSERT (p\<noteq>[]);
            case vo of 
              Some v \<Rightarrow> do {
                if v \<in> \<Union>(set p) then do {
                  \<comment> \<open>Collapse\<close>
                  let (a,p,D,pE) = gcollapse v (a,p,D,pE);

                  ASSERT (p\<noteq>[]);
                  ASSERT (a\<noteq>[]);

                  if last a = {0..<num_acc} then
                    RETURN (Some (\<Union>(set (butlast p)),last p),a,p,D,pE)
                  else
                    RETURN (None,a,p,D,pE)
                } else if v\<notin>D then do {
                  \<comment> \<open>Edge to new node. Append to path\<close>
                  RETURN (None,gpush v (a,p,D,pE))
                } else RETURN (None,a,p,D,pE)
              }
            | None \<Rightarrow> do {
                \<comment> \<open>No more outgoing edges from current node on path\<close>
                ASSERT (pE \<inter> last p \<times> UNIV = {});
                RETURN (None,gpop (a,p,D,pE))
              }
          }) s;
          ASSERT (brk=None \<longrightarrow> (p=[] \<and> pE={}));
          RETURN (gto_outer brk (a,p,D,pE))
        } else RETURN s0
    }) os;
    RETURN (goBrk os)
  }"

  lemma gcollapse_refine:
    "\<lbrakk>(v',v)\<in>Id; (s',s)\<in>gstate_rel\<rbrakk> 
      \<Longrightarrow> (gcollapse v' s',collapse v s)\<in>gstate_rel"
    unfolding gcollapse_def collapse_def collapse_aux_def gcollapse_aux_def 
    apply (simp add: gstate_rel_def br_def Let_def)
    unfolding gstate_invar_def[abs_def]
    apply (auto split: prod.splits simp: take_map drop_map)
    done

  lemma gpush_refine:
    "\<lbrakk>(v',v)\<in>Id; (s',s)\<in>gstate_rel\<rbrakk> \<Longrightarrow> (gpush v' s',push v s)\<in>gstate_rel"
    unfolding gpush_def push_def 
    apply (simp add: gstate_rel_def br_def)
    unfolding gstate_invar_def[abs_def]
    apply (auto split: prod.splits)
    done

  lemma gpop_refine:
    "\<lbrakk>(s',s)\<in>gstate_rel\<rbrakk> \<Longrightarrow> (gpop s',pop s)\<in>gstate_rel"
    unfolding gpop_def pop_def 
    apply (simp add: gstate_rel_def br_def)
    unfolding gstate_invar_def[abs_def]
    apply (auto split: prod.splits simp: map_butlast)
    done

  lemma ginitial_refine:
    "(ginitial x (None, b), initial x b) \<in> gstate_rel"
    unfolding ginitial_def gstate_rel_def br_def gstate_invar_def initial_def
    by auto

  lemma oinitial_b_refine: "((None,{}),(None,{}))\<in>Id\<times>\<^sub>rId" by simp

  lemma gselect_edge_refine: "\<lbrakk>(s',s)\<in>gstate_rel\<rbrakk> \<Longrightarrow> gselect_edge s' 
    \<le>\<Down>(\<langle>Id\<rangle>option_rel \<times>\<^sub>r gstate_rel) (select_edge s)"
    unfolding gselect_edge_def select_edge_def
    apply (simp add: pw_le_iff refine_pw_simps prod_rel_sv
      split: prod.splits option.splits)

    apply (auto simp: gstate_rel_def br_def gstate_invar_def)
    done

  lemma last_acc_impl:
    assumes "p\<noteq>[]"
    assumes "((a',p',D',pE'),(p,D,pE))\<in>gstate_rel"
    shows "(last a' = {0..<num_acc}) = (\<forall>i<num_acc. \<exists>q\<in>last p. i\<in>acc q)"
    using assms acc_bound unfolding gstate_rel_def br_def gstate_invar_def
    by (auto simp: last_map)

  lemma fglr_aux1:
    assumes V: "(v',v)\<in>Id" and S: "(s',s)\<in>gstate_rel" 
      and P: "\<And>a' p' D' pE' p D pE. ((a',p',D',pE'),(p,D,pE))\<in>gstate_rel 
      \<Longrightarrow> f' a' p' D' pE' \<le>\<Down>R (f p D pE)"
    shows "(let (a',p',D',pE') = gcollapse v' s' in f' a' p' D' pE') 
      \<le> \<Down>R (let (p,D,pE) = collapse v s in f p D pE)"
    apply (auto split: prod.splits)
    apply (rule P)
    using gcollapse_refine[OF V S]
    apply simp
    done

  lemma gstate_invar_empty: 
    "gstate_invar (a,[],D,pE) \<Longrightarrow> a=[]"
    "gstate_invar ([],p,D,pE) \<Longrightarrow> p=[]"
    by (auto simp add: gstate_invar_def)

  lemma find_ce_refine: "gfind_ce \<le>\<Down>Id find_ce"
    unfolding gfind_ce_def find_ce_def
    unfolding goinitial_def go_is_no_brk_def[abs_def] goD_def goBrk_def 
      gto_outer_def
    using [[goals_limit = 1]]
    apply (refine_rcg 
      gselect_edge_refine prod_relI[OF IdI gpop_refine]
      prod_relI[OF IdI gpush_refine]
      fglr_aux1 last_acc_impl oinitial_b_refine
      inj_on_id
    )
    apply refine_dref_type
    apply (simp_all add: ginitial_refine)
    apply (vc_solve (nopre) 
      solve: asm_rl 
      simp: gstate_rel_def br_def gstate_invar_empty)
    done
end

subsection \<open>Refinement to Gabow's Data Structure\<close>

subsubsection \<open>Preliminaries\<close>
definition Un_set_drop_impl :: "nat \<Rightarrow> 'a set list \<Rightarrow> 'a set nres"
  \<comment> \<open>Executable version of @{text "\<Union>set (drop i A)"}, using indexing to
  access @{text "A"}\<close>
  where "Un_set_drop_impl i A \<equiv> 
  do {
    (_,res) \<leftarrow> WHILET (\<lambda>(i,res). i < length A) (\<lambda>(i,res). do {
      ASSERT (i<length A);
      let res = A!i \<union> res;
      let i = i + 1;
      RETURN (i,res)
    }) (i,{});
    RETURN res
  }"

lemma Un_set_drop_impl_correct: 
  "Un_set_drop_impl i A \<le> SPEC (\<lambda>r. r=\<Union>(set (drop i A)))"
  unfolding Un_set_drop_impl_def
  apply (refine_rcg 
    WHILET_rule[where I="\<lambda>(i',res). res=\<Union>(set ((drop i (take i' A)))) \<and> i\<le>i'" 
    and R="measure (\<lambda>(i',_). length A - i')"] 
    refine_vcg)
  apply (auto simp: take_Suc_conv_app_nth)
  done

schematic_goal Un_set_drop_code_aux: 
  assumes [autoref_rules]: "(es_impl,{})\<in>\<langle>R\<rangle>Rs"
  assumes [autoref_rules]: "(un_impl,(\<union>))\<in>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs"
  shows "(?c,Un_set_drop_impl)\<in>nat_rel \<rightarrow> \<langle>\<langle>R\<rangle>Rs\<rangle>as_rel \<rightarrow> \<langle>\<langle>R\<rangle>Rs\<rangle>nres_rel"
  unfolding Un_set_drop_impl_def[abs_def]
  apply (autoref (trace, keep_goal))
  done
concrete_definition Un_set_drop_code uses Un_set_drop_code_aux

schematic_goal Un_set_drop_tr_aux: 
  "RETURN ?c \<le> Un_set_drop_code es_impl un_impl i A"
  unfolding Un_set_drop_code_def
  by refine_transfer
concrete_definition Un_set_drop_tr for es_impl un_impl i A 
  uses Un_set_drop_tr_aux 

lemma Un_set_drop_autoref[autoref_rules]: 
  assumes "GEN_OP es_impl {} (\<langle>R\<rangle>Rs)"
  assumes "GEN_OP un_impl (\<union>) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  shows "(\<lambda>i A. RETURN (Un_set_drop_tr es_impl un_impl i A),Un_set_drop_impl)
    \<in>nat_rel \<rightarrow> \<langle>\<langle>R\<rangle>Rs\<rangle>as_rel \<rightarrow> \<langle>\<langle>R\<rangle>Rs\<rangle>nres_rel"
  apply (intro fun_relI nres_relI)
  apply (rule order_trans[OF Un_set_drop_tr.refine])
  using Un_set_drop_code.refine[of es_impl Rs R un_impl, 
    param_fo, THEN nres_relD]
  using assms
  by simp


subsubsection \<open>Actual Refinement\<close>

type_synonym 'Q gGS = "nat set list \<times> 'Q GS"

type_synonym 'Q goGS = "'Q ce \<times> 'Q oGS"

context igb_graph
begin

definition gGS_invar :: "'Q gGS \<Rightarrow> bool"
  where "gGS_invar s \<equiv> 
  let (a,S,B,I,P) = s in 
    GS_invar (S,B,I,P)
    \<and> length a = length B
    \<and> \<Union>(set a) \<subseteq> {0..<num_acc}
  "

definition gGS_\<alpha> :: "'Q gGS \<Rightarrow> 'Q abs_gstate"
  where "gGS_\<alpha> s \<equiv> let (a,s)=s in (a,GS.\<alpha> s)"

definition "gGS_rel \<equiv> br gGS_\<alpha> gGS_invar"

lemma gGS_rel_sv[relator_props,intro!,simp]: "single_valued gGS_rel"
  unfolding gGS_rel_def by auto


definition goGS_invar :: "'Q goGS \<Rightarrow> bool" where
  "goGS_invar s \<equiv> let (brk,ogs)=s in brk=None \<longrightarrow> oGS_invar ogs"

definition "goGS_\<alpha> s \<equiv> let (brk,ogs)=s in (brk,oGS_\<alpha> ogs)"

definition "goGS_rel \<equiv> br goGS_\<alpha> goGS_invar"

lemma goGS_rel_sv[relator_props,intro!,simp]: "single_valued goGS_rel"
  unfolding goGS_rel_def by auto

end


context igb_fr_graph
begin
  lemma gGS_relE:
    assumes "(s',(a,p,D,pE))\<in>gGS_rel"
    obtains S' B' I' P' where "s'=(a,S',B',I',P')" 
      and "((S',B',I',P'),(p,D,pE))\<in>GS_rel" 
      and "length a = length B'"
      and "\<Union>(set a) \<subseteq> {0..<num_acc}"
    using assms
    apply (cases s')
    apply (simp add: gGS_rel_def br_def gGS_\<alpha>_def GS.\<alpha>_def)
    apply (rule that)
    apply (simp only:)
    apply (auto simp: GS_rel_def br_def gGS_invar_def GS.\<alpha>_def)
    done


  definition goinitial_impl :: "'Q goGS" 
    where "goinitial_impl \<equiv> (None,Map.empty)"
  lemma goinitial_impl_refine: "(goinitial_impl,goinitial)\<in>goGS_rel"
    by (auto 
      simp: goinitial_impl_def goinitial_def goGS_rel_def br_def 
      simp: goGS_\<alpha>_def goGS_invar_def oGS_\<alpha>_def oGS_invar_def)

  definition gto_outer_impl :: "'Q ce \<Rightarrow> 'Q gGS \<Rightarrow> 'Q goGS"
    where "gto_outer_impl brk s \<equiv> let (A,S,B,I,P)=s in (brk,I)"

  lemma gto_outer_refine:
    assumes A: "brk = None \<longrightarrow> (p=[] \<and> pE={})"
    assumes B: "(s, (A,p, D, pE)) \<in> gGS_rel"
    assumes C: "(brk',brk)\<in>Id"
    shows "(gto_outer_impl brk' s,gto_outer brk (A,p,D,pE))\<in>goGS_rel"
  proof (cases s)
    fix A S B I P
    assume [simp]: "s=(A,S,B,I,P)"
    show ?thesis
      using C
      apply (cases brk)
      using assms I_to_outer[of S B I P D]
      apply (auto 
        simp: goGS_rel_def br_def goGS_\<alpha>_def gto_outer_def 
              gto_outer_impl_def goGS_invar_def 
        simp: gGS_rel_def oGS_rel_def GS_rel_def gGS_\<alpha>_def gGS_invar_def 
              GS.\<alpha>_def) []

      using B apply (auto 
        simp: gto_outer_def gto_outer_impl_def
        simp: br_def goGS_rel_def goGS_invar_def goGS_\<alpha>_def oGS_\<alpha>_def
        simp: gGS_rel_def gGS_\<alpha>_def GS.\<alpha>_def GS.D_\<alpha>_def
      )

      done
  qed

  definition "gpush_impl v s \<equiv> let (a,s)=s in (a@[acc v], push_impl v s)"


  lemma gpush_impl_refine:
    assumes B: "(s',(a,p,D,pE))\<in>gGS_rel"
    assumes A: "(v',v)\<in>Id" 
    assumes PRE: "v' \<notin> \<Union>(set p)" "v' \<notin> D"
    shows "(gpush_impl v' s', gpush v (a,p,D,pE))\<in>gGS_rel"
  proof -
    from B obtain S' B' I' P' where [simp]: "s'=(a,S',B',I',P')" 
      and OSR: "((S',B',I',P'),(p,D,pE))\<in>GS_rel" and L: "length a = length B'" 
      and R: "\<Union>(set a) \<subseteq> {0..<num_acc}"
      by (rule gGS_relE)
    {
      fix S B I P S' B' I' P'
      assume "push_impl v (S, B, I, P) = (S', B', I', P')"
      hence "length B' = Suc (length B)" 
        by (auto simp add: push_impl_def GS.push_impl_def Let_def)  
    } note AUX1=this

    from push_refine[OF OSR A PRE] A L acc_bound R show ?thesis
      unfolding gpush_impl_def gpush_def
        gGS_rel_def gGS_invar_def gGS_\<alpha>_def GS_rel_def br_def
      apply (auto dest: AUX1)
      done
  qed
  
  definition gpop_impl :: "'Q gGS \<Rightarrow> 'Q gGS nres" 
    where "gpop_impl s \<equiv> do {
    let (a,s)=s;
    s\<leftarrow>pop_impl s;
    ASSERT (a\<noteq>[]);
    let a = butlast a;
    RETURN (a,s)
  }"

  lemma gpop_impl_refine:
    assumes A: "(s',(a,p,D,pE))\<in>gGS_rel"
    assumes PRE: "p \<noteq> []" "pE \<inter> last p \<times> UNIV = {}"
    shows "gpop_impl s' \<le> \<Down>gGS_rel (RETURN (gpop (a,p,D,pE)))"
  proof -
    from A obtain S' B' I' P' where [simp]: "s'=(a,S',B',I',P')" 
      and OSR: "((S',B',I',P'),(p,D,pE))\<in>GS_rel" and L: "length a = length B'"
      and R: "\<Union>(set a) \<subseteq> {0..<num_acc}"
      by (rule gGS_relE)

    from PRE OSR have [simp]: "a\<noteq>[]" using L
      by (auto simp add: GS_rel_def br_def GS.\<alpha>_def GS.p_\<alpha>_def)

    {
      fix S B I P S' B' I' P'
      assume "nofail (pop_impl ((S, B, I, P)::'a GS))"
        "inres (pop_impl ((S, B, I, P)::'a GS)) (S', B', I', P')"
      hence "length B' = length B - Suc 0"
        apply (simp add: pop_impl_def GS.pop_impl_def Let_def
          refine_pw_simps)
        apply auto
        done
    } note AUX1=this

    from A L show ?thesis
      unfolding gpop_impl_def gpop_def gGS_rel_def gGS_\<alpha>_def br_def
      apply (simp add: Let_def)
      using pop_refine[OF OSR PRE]
      apply (simp add: pw_le_iff refine_pw_simps split: prod.splits)
      unfolding gGS_rel_def gGS_invar_def gGS_\<alpha>_def GS_rel_def GS.\<alpha>_def br_def
      apply (auto dest!: AUX1 in_set_butlastD iff: Sup_le_iff)
      done
  qed
  
  definition gselect_edge_impl :: "'Q gGS \<Rightarrow> ('Q option \<times> 'Q gGS) nres" 
    where "gselect_edge_impl s \<equiv> 
    do { 
      let (a,s)=s; 
      (vo,s)\<leftarrow>select_edge_impl s; 
      RETURN (vo,a,s)
    }"

  thm select_edge_refine
  lemma gselect_edge_impl_refine:
    assumes A: "(s', a, p, D, pE) \<in> gGS_rel" 
    assumes PRE: "p \<noteq> []"
    shows "gselect_edge_impl s' \<le> \<Down>(Id \<times>\<^sub>r gGS_rel) (gselect_edge (a, p, D, pE))"
  proof -
    from A obtain S' B' I' P' where [simp]: "s'=(a,S',B',I',P')" 
      and OSR: "((S',B',I',P'),(p,D,pE))\<in>GS_rel" and L: "length a = length B'"
      and R: "\<Union>(set a) \<subseteq> {0..<num_acc}"
      by (rule gGS_relE)

    {
      fix S B I P S' B' I' P' vo
      assume "nofail (select_edge_impl ((S, B, I, P)::'a GS))"
        "inres (select_edge_impl ((S, B, I, P)::'a GS)) (vo, (S', B', I', P'))"
      hence "length B' = length B"
        apply (simp add: select_edge_impl_def GS.sel_rem_last_def refine_pw_simps
          split: if_split_asm prod.splits)
        apply auto
        done
    } note AUX1=this

    show ?thesis
      using select_edge_refine[OF OSR PRE]
      unfolding gselect_edge_impl_def gselect_edge_def
      apply (simp add: refine_pw_simps pw_le_iff prod_rel_sv)

      unfolding gGS_rel_def br_def gGS_\<alpha>_def gGS_invar_def GS_rel_def GS.\<alpha>_def
      apply (simp split: prod.splits)
      apply clarsimp
      using R
      apply (auto simp: L dest: AUX1)
      done
  qed


  term GS.idx_of_impl

  thm GS_invar.idx_of_correct


  definition gcollapse_impl_aux :: "'Q \<Rightarrow> 'Q gGS \<Rightarrow> 'Q gGS nres" where 
    "gcollapse_impl_aux v s \<equiv> 
    do { 
      let (A,s)=s;
      \<^cancel>\<open>ASSERT (v\<in>\<Union>set (GS.p_\<alpha> s));\<close>
      i \<leftarrow> GS.idx_of_impl s v;
      s \<leftarrow> collapse_impl v s;
      ASSERT (i < length A);
      us \<leftarrow> Un_set_drop_impl i A;
      let A = take i A @ [us];
      RETURN (A,s)
    }"

  term collapse
  lemma gcollapse_alt:
    "gcollapse v APDPE = ( 
      let 
        (a,p,D,pE)=APDPE; 
        i=idx_of p v;
        s=collapse v (p,D,pE);
        us=\<Union>(set (drop i a));
        a = take i a @ [us]
      in (a,s))"
    unfolding gcollapse_def gcollapse_aux_def collapse_def collapse_aux_def
    by auto

  thm collapse_refine
  lemma gcollapse_impl_aux_refine:
    assumes A: "(s', a, p, D, pE) \<in> gGS_rel" 
    assumes B: "(v',v)\<in>Id"
    assumes PRE: "v\<in>\<Union>(set p)"
    shows "gcollapse_impl_aux v' s' 
      \<le> \<Down> gGS_rel (RETURN (gcollapse v (a, p, D, pE)))"
  proof -
    note [simp] = Let_def

    from A obtain S' B' I' P' where [simp]: "s'=(a,S',B',I',P')" 
      and OSR: "((S',B',I',P'),(p,D,pE))\<in>GS_rel" and L: "length a = length B'"
      and R: "\<Union>(set a) \<subseteq> {0..<num_acc}"
      by (rule gGS_relE)

    from B have [simp]: "v'=v" by simp

    from OSR have [simp]: "GS.p_\<alpha> (S',B',I',P') = p"
      by (simp add: GS_rel_def br_def GS.\<alpha>_def)

    from OSR PRE have PRE': "v \<in> \<Union>(set (GS.p_\<alpha> (S',B',I',P')))"
      by (simp add: GS_rel_def br_def GS.\<alpha>_def)

    from OSR have GS_invar: "GS_invar (S',B',I',P')" 
      by (simp add: GS_rel_def br_def)

    term GS.B
    {
      fix s
      assume "collapse v (p, D, pE) = (GS.p_\<alpha> s, GS.D_\<alpha> s, GS.pE_\<alpha> s)"
      hence "length (GS.B s) = Suc (idx_of p v)"
        unfolding collapse_def collapse_aux_def Let_def
        apply (cases s)
        apply (auto simp: GS.p_\<alpha>_def)
        apply (drule arg_cong[where f=length])
        using GS_invar.p_\<alpha>_disjoint_sym[OF GS_invar]
          and PRE \<open>GS.p_\<alpha> (S', B', I', P') = p\<close> idx_of_props(1)[of p v]
        by simp
    } note AUX1 = this

    show ?thesis
      unfolding gcollapse_alt gcollapse_impl_aux_def
      apply simp
      apply (rule RETURN_as_SPEC_refine)
      apply (refine_rcg
        order_trans[OF GS_invar.idx_of_correct[OF GS_invar PRE']] 
        order_trans[OF collapse_refine[OF OSR B PRE, simplified]]
        refine_vcg
      )
      using PRE' apply simp
      
      apply (simp add: L)

      using Un_set_drop_impl_correct acc_bound R
      apply (simp add: refine_pw_simps pw_le_iff)
      unfolding gGS_rel_def GS_rel_def GS.\<alpha>_def br_def gGS_\<alpha>_def gGS_invar_def
      apply (clarsimp simp: L dest!: AUX1)
      apply (auto dest!: AUX1 simp: L)
      apply (force dest!: in_set_dropD) []
      apply (force dest!: in_set_takeD) []
      done
  qed

  definition gcollapse_impl :: "'Q \<Rightarrow> 'Q gGS \<Rightarrow> 'Q gGS nres" 
    where "gcollapse_impl v s \<equiv>     
    do { 
      let (A,S,B,I,P)=s;
      i \<leftarrow> GS.idx_of_impl (S,B,I,P) v;
      ASSERT (i+1 \<le> length B);
      let B = take (i+1) B;
      ASSERT (i < length A);
      us\<leftarrow>Un_set_drop_impl i A;
      let A = take i A @ [us];
      RETURN (A,S,B,I,P)
    }"

  lemma gcollapse_impl_aux_opt_refine: 
    "gcollapse_impl v s \<le> gcollapse_impl_aux v s"
    unfolding gcollapse_impl_def gcollapse_impl_aux_def collapse_impl_def 
      GS.collapse_impl_def
    apply (simp add: refine_pw_simps pw_le_iff split: prod.splits) 
    apply blast
    done
  
  lemma gcollapse_impl_refine:
    assumes A: "(s', a, p, D, pE) \<in> gGS_rel" 
    assumes B: "(v',v)\<in>Id"
    assumes PRE: "v\<in>\<Union>(set p)"
    shows "gcollapse_impl v' s' 
    \<le> \<Down> gGS_rel (RETURN (gcollapse v (a, p, D, pE)))"
    using order_trans[OF 
      gcollapse_impl_aux_opt_refine 
      gcollapse_impl_aux_refine[OF assms]]
    .

  definition ginitial_impl :: "'Q \<Rightarrow> 'Q goGS \<Rightarrow> 'Q gGS" 
    where "ginitial_impl v0 s0 \<equiv> ([acc v0],initial_impl v0 (snd s0))"
  lemma ginitial_impl_refine: 
    assumes A: "v0\<notin>goD s0" "go_is_no_brk s0"
    assumes REL: "(s0i,s0)\<in>goGS_rel" "(v0i,v0)\<in>Id" 
    shows "(ginitial_impl v0i s0i,ginitial v0 s0)\<in>gGS_rel"
    unfolding ginitial_impl_def ginitial_def 
    using REL initial_refine[OF A(1) _ REL(2), of "snd s0i"] A(2)
    apply (auto 
      simp: gGS_rel_def br_def gGS_\<alpha>_def gGS_invar_def goGS_rel_def goGS_\<alpha>_def
      simp: go_is_no_brk_def goD_def oGS_rel_def GS_rel_def goGS_invar_def
      split: prod.splits

    )
    using acc_bound
    apply (fastforce simp: initial_impl_def GS_initial_impl_def)+
    done

  definition gpath_is_empty_impl :: "'Q gGS \<Rightarrow> bool"
    where "gpath_is_empty_impl s = path_is_empty_impl (snd s)"

  lemma gpath_is_empty_refine: 
    "(s,(a,p,D,pE))\<in>gGS_rel \<Longrightarrow> gpath_is_empty_impl s \<longleftrightarrow> p=[]"
    unfolding gpath_is_empty_impl_def 
    using path_is_empty_refine
    by (fastforce simp: gGS_rel_def br_def gGS_invar_def gGS_\<alpha>_def GS.\<alpha>_def)

  definition gis_on_stack_impl :: "'Q \<Rightarrow> 'Q gGS \<Rightarrow> bool" 
    where "gis_on_stack_impl v s = is_on_stack_impl v (snd s)"

  lemma gis_on_stack_refine: 
    "\<lbrakk>(s,(a,p,D,pE))\<in>gGS_rel\<rbrakk> \<Longrightarrow> gis_on_stack_impl v s \<longleftrightarrow> v\<in>\<Union>(set p)"
    unfolding gis_on_stack_impl_def 
    using is_on_stack_refine
    by (fastforce simp: gGS_rel_def br_def gGS_invar_def gGS_\<alpha>_def GS.\<alpha>_def)

  definition gis_done_impl :: "'Q \<Rightarrow> 'Q gGS \<Rightarrow> bool"
    where "gis_done_impl v s \<equiv> is_done_impl v (snd s)"
  thm is_done_refine
  lemma gis_done_refine: "(s,(a,p,D,pE))\<in>gGS_rel 
    \<Longrightarrow> gis_done_impl v s \<longleftrightarrow> (v \<in> D)"
    using is_done_refine[of "(snd s)" v]
    by (auto 
      simp: gGS_rel_def br_def gGS_\<alpha>_def gGS_invar_def GS.\<alpha>_def 
            gis_done_impl_def)


  definition (in -) "on_stack_less I u v \<equiv> 
    case I v of 
      Some (STACK j) \<Rightarrow> j<u
    | _ \<Rightarrow> False"

  definition (in -) "on_stack_ge I l v \<equiv> 
    case I v of 
      Some (STACK j) \<Rightarrow> l\<le>j
    | _ \<Rightarrow> False"


  lemma (in GS_invar) set_butlast_p_refine:
    assumes PRE: "p_\<alpha>\<noteq>[]"
    shows "Collect (on_stack_less I (last B)) = \<Union>(set (butlast p_\<alpha>))" (is "?L=?R")
  proof (intro equalityI subsetI)
    from PRE have [simp]: "B\<noteq>[]" by (auto simp: p_\<alpha>_def)

    have [simp]: "S\<noteq>[]"
      by (simp add: empty_eq)

    {
      fix v
      assume "v\<in>?L"
      then obtain j where [simp]: "I v = Some (STACK j)" and "j<last B"
        by (auto simp: on_stack_less_def split: option.splits node_state.splits)

      from I_consistent[of v j] have [simp]: "j<length S" "v=S!j" by auto
      
      from B0 have "B!0=0" by simp
      from \<open>j<last B\<close> have "j<B!(length B - 1)" by (simp add: last_conv_nth)
      from find_seg_bounds[OF \<open>j<length S\<close>] find_seg_correct[OF \<open>j<length S\<close>]
      have "v\<in>seg (find_seg j)" "find_seg j < length B" by auto
      moreover with \<open>j<B!(length B - 1)\<close> have "find_seg j < length B - 1"
        (* What follows is an unreadable, auto-generated structured proof
          that replaces the following smt-call:
        by (smt GS.seg_start_def `seg_start (find_seg j) \<le> j`)*)
      proof -
        have f1: "\<And>x\<^sub>1 x. \<not> (x\<^sub>1::nat) < x\<^sub>1 - x"
          using less_imp_diff_less by blast
        have "j \<le> last B"
          by (metis \<open>j < last B\<close> less_le)
        hence f2: "\<And>x\<^sub>1. \<not> last B < x\<^sub>1 \<or> \<not> x\<^sub>1 \<le> j"
          using f1 by (metis diff_diff_cancel le_trans)
        have "\<And>x\<^sub>1. seg_end x\<^sub>1 \<le> j \<or> \<not> x\<^sub>1 < find_seg j"
          by (metis \<open>seg_start (find_seg j) \<le> j\<close> calculation(2) 
            le_trans seg_end_less_start)
        thus "find_seg j < length B - 1"
          using f1 f2 
          by (metis GS.seg_start_def \<open>B \<noteq> []\<close> \<open>j < B ! (length B - 1)\<close>
            \<open>seg_start (find_seg j) \<le> j\<close> calculation(2) diff_diff_cancel 
            last_conv_nth nat_neq_iff seg_start_less_end)
      qed
      ultimately show "v\<in>?R" 
        by (auto simp: p_\<alpha>_def map_butlast[symmetric] butlast_upt)
    }

    {
      fix v
      assume "v\<in>?R"
      then obtain i where "i<length B - 1" and "v\<in>seg i"
        by (auto simp: p_\<alpha>_def map_butlast[symmetric] butlast_upt)
      then obtain j where "j < seg_end i" and "v=S!j"
        by (auto simp: seg_def)
      hence "j<B!(i+1)" and "i+1 \<le> length B - 1" using \<open>i<length B - 1\<close>
        by (auto simp: seg_end_def last_conv_nth split: if_split_asm)
      with sorted_nth_mono[OF B_sorted \<open>i+1 \<le> length B - 1\<close>] have "j<last B"
        by (auto simp: last_conv_nth)
      moreover from \<open>j < seg_end i\<close> have "j<length S"
        by (metis GS.seg_end_def add_diff_inverse_nat \<open>i + 1 \<le> length B - 1\<close>
          add_lessD1 less_imp_diff_less less_le_not_le nat_neq_iff 
          seg_end_bound)
        (*by (smt `i < length B - 1` seg_end_bound)*)
      with I_consistent \<open>v=S!j\<close> have "I v = Some (STACK j)" by auto
      ultimately show "v\<in>?L"
        by (auto simp: on_stack_less_def)
    }
  qed

  lemma (in GS_invar) set_last_p_refine:
    assumes PRE: "p_\<alpha>\<noteq>[]"
    shows "Collect (on_stack_ge I (last B)) = last p_\<alpha>" (is "?L=?R")
  proof (intro equalityI subsetI)
    from PRE have [simp]: "B\<noteq>[]" by (auto simp: p_\<alpha>_def)

    have [simp]: "S\<noteq>[]" by (simp add: empty_eq)

    {
      fix v
      assume "v\<in>?L"
      then obtain j where [simp]: "I v = Some (STACK j)" and "j\<ge>last B"
        by (auto simp: on_stack_ge_def split: option.splits node_state.splits)

      from I_consistent[of v j] have [simp]: "j<length S" "v=S!j" by auto
      hence "v\<in>seg (length B - 1)" using \<open>j\<ge>last B\<close>
        by (auto simp: seg_def last_conv_nth seg_start_def seg_end_def)
      thus "v\<in>last p_\<alpha>" by (auto simp: p_\<alpha>_def last_map)
    }

    {
      fix v
      assume "v\<in>?R"
      hence "v\<in>seg (length B - 1)"
        by (auto simp: p_\<alpha>_def last_map)
      then obtain j where "v=S!j" "j\<ge>last B" "j<length S"
        by (auto simp: seg_def last_conv_nth seg_start_def seg_end_def)
      with I_consistent have "I v = Some (STACK j)" by simp
      with \<open>j\<ge>last B\<close> show "v\<in>?L" by (auto simp: on_stack_ge_def)
    }
  qed

  definition ce_impl :: "'Q gGS \<Rightarrow> (('Q set \<times> 'Q set) option \<times> 'Q gGS) nres"
    where "ce_impl s \<equiv> 
    do {
      let (a,S,B,I,P) = s;
      ASSERT (B\<noteq>[]);
      let bls = Collect (on_stack_less I (last B));
      let ls = Collect (on_stack_ge I (last B));
      RETURN (Some (bls, ls),a,S,B,I,P)
    }"

  lemma ce_impl_refine:
    assumes A: "(s,(a,p,D,pE))\<in>gGS_rel"
    assumes PRE: "p\<noteq>[]"
    shows "ce_impl s \<le> \<Down>(Id\<times>\<^sub>rgGS_rel) 
      (RETURN (Some (\<Union>(set (butlast p)),last p),a,p,D,pE))"
  proof -
    from A obtain S' B' I' P' where [simp]: "s=(a,S',B',I',P')" 
      and OSR: "((S',B',I',P'),(p,D,pE))\<in>GS_rel" and L: "length a = length B'"
      by (rule gGS_relE)

    from OSR have [simp]: "GS.p_\<alpha> (S',B',I',P') = p"
      by (simp add: GS_rel_def br_def GS.\<alpha>_def)

    from PRE have NE': "GS.p_\<alpha> (S', B', I', P') \<noteq> []" by simp
    hence BNE[simp]: "B'\<noteq>[]" by (simp add: GS.p_\<alpha>_def)

    from OSR have GS_invar: "GS_invar (S',B',I',P')" 
      by (simp add: GS_rel_def br_def)

    show ?thesis
      using GS_invar.set_butlast_p_refine[OF GS_invar NE']
      using GS_invar.set_last_p_refine[OF GS_invar NE']
      unfolding ce_impl_def
      using A
      by auto
  qed

  definition "last_is_acc_impl s \<equiv> 
    do {
      let (a,_)=s;
      ASSERT (a\<noteq>[]);
      RETURN (\<forall>i<num_acc. i\<in>last a)
    }"

  lemma last_is_acc_impl_refine:
    assumes A: "(s,(a,p,D,pE))\<in>gGS_rel"
    assumes PRE: "a\<noteq>[]"
    shows "last_is_acc_impl s \<le> RETURN (last a = {0..<num_acc})"
  proof -
    from A PRE have "last a \<subseteq> {0..<num_acc}"
      unfolding gGS_rel_def gGS_invar_def br_def gGS_\<alpha>_def by auto
    hence C: "(\<forall>i<num_acc. i\<in>last a) \<longleftrightarrow> (last a = {0..<num_acc})"
      by auto

    from A obtain gs where [simp]: "s=(a,gs)"
      by (auto simp: gGS_rel_def gGS_\<alpha>_def br_def split: prod.splits)

    show ?thesis
      unfolding last_is_acc_impl_def 
      by (auto simp: gGS_rel_def br_def gGS_\<alpha>_def C PRE split: prod.splits)
  qed

  definition go_is_no_brk_impl :: "'Q goGS \<Rightarrow> bool" 
    where "go_is_no_brk_impl s \<equiv> fst s = None"
  lemma go_is_no_brk_refine: 
    "(s,s')\<in>goGS_rel \<Longrightarrow> go_is_no_brk_impl s \<longleftrightarrow> go_is_no_brk s'"
    unfolding go_is_no_brk_def go_is_no_brk_impl_def
    by (auto simp: goGS_rel_def br_def goGS_\<alpha>_def split: prod.splits)

  definition goD_impl :: "'Q goGS \<Rightarrow> 'Q oGS" where "goD_impl s \<equiv> snd s"
  lemma goD_refine: 
    "go_is_no_brk s' \<Longrightarrow> (s,s')\<in>goGS_rel \<Longrightarrow> (goD_impl s, goD s')\<in>oGS_rel"
    unfolding goD_impl_def goD_def
    by (auto 
      simp: goGS_rel_def br_def goGS_\<alpha>_def goGS_invar_def oGS_rel_def 
            go_is_no_brk_def) 

  definition go_is_done_impl :: "'Q \<Rightarrow> 'Q goGS \<Rightarrow> bool" 
    where "go_is_done_impl v s \<equiv> is_done_oimpl v (snd s)"
  thm is_done_orefine
  lemma go_is_done_impl_refine: "\<lbrakk>go_is_no_brk s'; (s,s')\<in>goGS_rel; (v,v')\<in>Id\<rbrakk> 
    \<Longrightarrow> go_is_done_impl v s \<longleftrightarrow> (v'\<in>goD s')"
    using is_done_orefine
    unfolding go_is_done_impl_def goD_def go_is_no_brk_def
    apply (fastforce simp: goGS_rel_def br_def goGS_invar_def goGS_\<alpha>_def)
    done


  definition goBrk_impl :: "'Q goGS \<Rightarrow> 'Q ce" where "goBrk_impl \<equiv> fst"

  lemma goBrk_refine: "(s,s')\<in>goGS_rel \<Longrightarrow> (goBrk_impl s, goBrk s')\<in>Id"
    unfolding goBrk_impl_def goBrk_def
    by (auto simp: goGS_rel_def br_def goGS_\<alpha>_def split: prod.splits)

  definition find_ce_impl :: "('Q set \<times> 'Q set) option nres" where
    "find_ce_impl \<equiv> do {
      stat_start_nres;
      let os=goinitial_impl;
      os\<leftarrow>FOREACHci (\<lambda>it os. fgl_outer_invar it (goGS_\<alpha> os)) V0 
        (go_is_no_brk_impl) (\<lambda>v0 s0. 
      do {
        if \<not>go_is_done_impl v0 s0 then do {

          let s = (None,ginitial_impl v0 s0);

          (brk,s)\<leftarrow>WHILEIT 
            (\<lambda>(brk,s). fgl_invar v0 (oGS_\<alpha> (goD_impl s0)) (brk,snd (gGS_\<alpha> s)))
            (\<lambda>(brk,s). brk=None \<and> \<not>gpath_is_empty_impl s) (\<lambda>(l,s).
          do {
            \<comment> \<open>Select edge from end of path\<close>
            (vo,s) \<leftarrow> gselect_edge_impl s;

            case vo of 
              Some v \<Rightarrow> do {
                if gis_on_stack_impl v s then do {
                  s\<leftarrow>gcollapse_impl v s;
                  b\<leftarrow>last_is_acc_impl s;
                  if b then
                    ce_impl s
                  else 
                    RETURN (None,s)
                } else if \<not>gis_done_impl v s then do {
                  \<comment> \<open>Edge to new node. Append to path\<close>
                  RETURN (None,gpush_impl v s)
                } else do {
                  \<comment> \<open>Edge to done node. Skip\<close>
                  RETURN (None,s)
                }
              }
            | None \<Rightarrow> do {
                \<comment> \<open>No more outgoing edges from current node on path\<close>
                s\<leftarrow>gpop_impl s;
                RETURN (None,s)
              }
          }) (s);
          RETURN (gto_outer_impl brk s)
        } else RETURN s0
      }) os;
      stat_stop_nres;
      RETURN (goBrk_impl os)
    }"

  lemma find_ce_impl_refine: "find_ce_impl \<le> \<Down>Id gfind_ce"
  proof -
    note [refine2] = prod_relI[OF IdI[of None] ginitial_impl_refine]

    have [refine]: "\<And>s a p D pE. \<lbrakk>
      (s,(a,p,D,pE))\<in>gGS_rel;
      p \<noteq> []; pE \<inter> last p \<times> UNIV = {}
      \<rbrakk> \<Longrightarrow>
      gpop_impl s \<bind> (\<lambda>s. RETURN (None, s))
        \<le> SPEC (\<lambda>c. (c, None, gpop (a,p,D,pE)) \<in> Id \<times>\<^sub>r gGS_rel)"
      apply (drule (2) gpop_impl_refine)
      apply (fastforce simp add: pw_le_iff refine_pw_simps)
      done

    note [[goals_limit = 1]]

    note FOREACHci_refine_rcg'[refine del]

    show ?thesis
      unfolding find_ce_impl_def gfind_ce_def
      apply (refine_rcg
        bind_refine'
        prod_relI IdI
        inj_on_id

        gselect_edge_impl_refine gpush_impl_refine 
        oinitial_refine ginitial_impl_refine 
        bind_Let_refine2[OF gcollapse_impl_refine]
        if_bind_cond_refine[OF last_is_acc_impl_refine]
        ce_impl_refine
        goinitial_impl_refine
        gto_outer_refine
        goBrk_refine
        FOREACHci_refine_rcg'[where R=goGS_rel, OF inj_on_id]
      )

      apply refine_dref_type
    
      apply (simp_all add: go_is_no_brk_refine go_is_done_impl_refine)
      apply (auto simp: goGS_rel_def br_def) []
      apply (auto simp: goGS_rel_def br_def goGS_\<alpha>_def gGS_\<alpha>_def gGS_rel_def 
                        goD_def goD_impl_def) []

      apply (auto dest: gpath_is_empty_refine ) []
      apply (auto dest: gis_on_stack_refine) []
      apply (auto dest: gis_done_refine) []
      done
  qed

end

section \<open>Constructing a Lasso from Counterexample\<close>

subsection \<open>Lassos in GBAs\<close>

context igb_fr_graph begin

  definition reconstruct_reach :: "'Q set \<Rightarrow> 'Q set \<Rightarrow> ('Q list \<times> 'Q) nres"
    \<comment> \<open>Reconstruct the reaching path of a lasso\<close>
    where "reconstruct_reach Vr Vl \<equiv> do {
      res \<leftarrow> find_path (E\<inter>Vr\<times>UNIV) V0 (\<lambda>v. v\<in>Vl);
      ASSERT (res \<noteq> None);
      RETURN (the res)
    }"

  lemma reconstruct_reach_correct:
    assumes CEC: "ce_correct Vr Vl"
    shows "reconstruct_reach Vr Vl 
      \<le> SPEC (\<lambda>(pr,va). \<exists>v0\<in>V0. path E v0 pr va \<and> va\<in>Vl)"
  proof -
    have FIN_aux: "finite ((E \<inter> Vr \<times> UNIV)\<^sup>* `` V0)"
      by (metis finite_reachableE_V0 finite_subset inf_sup_ord(1) inf_sup_ord(2)
        inf_top.left_neutral reachable_mono)
    
    {
      fix u p v
      assume P: "path E u p v" and SS: "set p \<subseteq> Vr"
      have "path (E \<inter> Vr\<times>UNIV) u p v"
        apply (rule path_mono[OF _ path_restrict[OF P]])
        using SS by auto
    } note P_CONV=this

    from CEC obtain v0 "pr" va where "v0\<in>V0" "set pr \<subseteq> Vr" "va\<in>Vl" 
      "path (E \<inter> Vr\<times>UNIV) v0 pr va"
      unfolding ce_correct_def is_lasso_prpl_def is_lasso_prpl_pre_def
      by (force simp: neq_Nil_conv path_simps dest: P_CONV)
    hence 1: "va \<in> (E \<inter> Vr \<times> UNIV)\<^sup>* `` V0" 
      by (auto dest: path_is_rtrancl)
      
    show ?thesis
      using assms unfolding reconstruct_reach_def
      apply (refine_rcg refine_vcg order_trans[OF find_path_ex_rule])
      apply (clarsimp_all simp: FIN_aux finite_V0)

      using \<open>va\<in>Vl\<close> 1 apply auto []

      apply (auto dest: path_mono[of "E \<inter> Vr \<times> UNIV" E, simplified]) []
      done
  qed

  definition "rec_loop_invar Vl va s \<equiv> let (v,p,cS) = s in 
    va \<in> E\<^sup>*``V0 \<and>
    path E va p v \<and>
    cS = acc v \<union> (\<Union>(acc`set p)) \<and>
    va \<in> Vl \<and> v \<in> Vl \<and> set p \<subseteq> Vl"

  definition reconstruct_lasso :: "'Q set \<Rightarrow> 'Q set \<Rightarrow> ('Q list \<times> 'Q list) nres"
    \<comment> \<open>Reconstruct lasso\<close>
    where "reconstruct_lasso Vr Vl \<equiv> do {
    (pr,va) \<leftarrow> reconstruct_reach Vr Vl;
    
    let cS_full = {0..<num_acc};
    let E = E \<inter> UNIV\<times>Vl;
    
    (vd,p,_) \<leftarrow> WHILEIT (rec_loop_invar Vl va) 
      (\<lambda>(_,_,cS). cS \<noteq> cS_full) 
      (\<lambda>(v,p,cS). do {
        ASSERT (\<exists>v'. (v,v')\<in>E\<^sup>* \<and> \<not> (acc v' \<subseteq> cS));
        sr \<leftarrow> find_path E {v} (\<lambda>v. \<not> (acc v \<subseteq> cS));
        ASSERT (sr \<noteq> None);
        let (p_seg,v) = the sr;
        RETURN (v,p@p_seg,cS \<union> acc v)
      }) (va,[],acc va);

    p_close_r \<leftarrow> (if p=[] then 
        find_path1 E vd ((=) va)
      else
        find_path E {vd} ((=) va));

    ASSERT (p_close_r \<noteq> None);
    let (p_close,_) = the p_close_r;

    RETURN (pr, p@p_close)
  }"


lemma (in igb_fr_graph) reconstruct_lasso_correct:
  assumes CEC: "ce_correct Vr Vl"
  shows "reconstruct_lasso Vr Vl \<le> SPEC (is_lasso_prpl)"
proof -

  let ?E = "E \<inter> UNIV \<times> Vl"

  have E_SS: "E \<inter> Vl \<times> Vl \<subseteq> ?E" by auto

  from CEC have
    REACH: "Vl \<subseteq> E\<^sup>*``V0"
    and CONN: "Vl\<times>Vl \<subseteq> (E \<inter> Vl\<times>Vl)\<^sup>*"
    and NONTRIV: "Vl\<times>Vl \<inter> E \<noteq> {}"
    and NES[simp]: "Vl\<noteq>{}"
    and ALL: "\<Union>(acc`Vl) = {0..<num_acc}"
    unfolding ce_correct_def is_lasso_prpl_def
    apply clarsimp_all
    apply auto []
    apply force
    done

  define term_rel
    where "term_rel = (inv_image (finite_psupset {0..<num_acc}) (\<lambda>(_::'Q,_::'Q list,cS). cS))"
  hence WF: "wf term_rel" by simp

  { fix va
    assume "va \<in> Vl"
    hence "rec_loop_invar Vl va (va, [], acc va)"
      unfolding rec_loop_invar_def using REACH by auto
  } note INVAR_INITIAL = this

  {
    fix v p cS va
    assume "rec_loop_invar Vl va (v, p, cS)"
    hence "finite ((?E)\<^sup>* `` {v})"
      apply -
      apply (rule finite_subset[where B="E\<^sup>*``V0"])
      unfolding rec_loop_invar_def
      using REACH
      apply (clarsimp_all dest!: path_is_rtrancl)
      apply (drule rtrancl_mono_mp[where U="?E" and V=E, rotated], (auto) [])
      by (metis rev_ImageI rtrancl_trans)
  } note FIN1 = this

  {
    fix va v :: 'Q and p cS
    assume INV: "rec_loop_invar Vl va (v,p,cS)"
      and NC: "cS \<noteq> {0..<num_acc}"

    from NC INV obtain i where "i<num_acc" "i\<notin>cS" 
      unfolding rec_loop_invar_def by auto blast

    with ALL obtain v' where "v'\<in>Vl" "\<not> acc v' \<subseteq> cS"
      by simp (smt UN_iff atLeastLessThan_iff le0 subsetCE)
     
    moreover with CONN INV have "(v,v')\<in>(E \<inter> Vl \<times> Vl)\<^sup>*"
      unfolding rec_loop_invar_def by auto
    hence "(v,v')\<in>?E\<^sup>*" using rtrancl_mono_mp[OF E_SS] by blast
    ultimately have "\<exists>v'. (v,v')\<in>(?E)\<^sup>* \<and> \<not> acc v' \<subseteq> cS" by auto
  } note ASSERT1 = this

  {
    fix va v p cS v' p'
    assume "rec_loop_invar Vl va (v, p, cS)"
    and "path (?E) v p' v'"
    and "\<not> (acc v' \<subseteq> cS)"
    and "\<forall>v\<in>set p'. acc v \<subseteq> cS"
    hence "rec_loop_invar Vl va (v', p@p', cS \<union> acc v')"
      unfolding rec_loop_invar_def
      apply simp
      apply (intro conjI)
      apply (auto simp: path_simps dest: path_mono[of "?E" E, simplified]) []

      apply (cases p')
      apply (auto simp: path_simps) [2]

      apply (cases p' rule: rev_cases)
      apply (auto simp: path_simps) [2]

      apply (erule path_set_induct)
      apply auto [2]
      done
  } note INV_PRES = this

  {
    fix va v p cS v' p'
    assume "rec_loop_invar Vl va (v, p, cS)"
      and "path ?E v p' v'"
      and "\<not> (acc v' \<subseteq> cS)"
      and "\<forall>v\<in>set p'. acc v \<subseteq> cS"
    hence "((v', p@p', cS \<union> acc v'), (v,p,cS)) \<in> term_rel"
      unfolding term_rel_def rec_loop_invar_def
      by (auto simp: finite_psupset_def)
  } note VAR = this

  have CONN1: "Vl \<times> Vl \<subseteq> (?E)\<^sup>+"
  proof clarify
    fix a b
    assume "a\<in>Vl" "b\<in>Vl"
    from NONTRIV obtain u v where E: "(u,v)\<in>(E \<inter> Vl\<times>Vl)" by auto
    from CONN \<open>a\<in>Vl\<close> E have "(a,u)\<in>(E\<inter>Vl\<times>Vl)\<^sup>*" by auto
    also note E
    also (rtrancl_into_trancl1) from CONN \<open>b\<in>Vl\<close> E have "(v,b)\<in>(E\<inter>Vl\<times>Vl)\<^sup>*"
      by auto
    finally show "(a,b)\<in>(?E)\<^sup>+" using trancl_mono[OF _ E_SS] by auto
  qed
    
  {
    fix va v p cS
    assume "rec_loop_invar Vl va (v, p, cS)"
    hence "(v,va) \<in> (?E)\<^sup>+"
      unfolding rec_loop_invar_def
      using CONN1
      by auto
  } note CLOSE1 = this

  {
    fix va v p cS
    assume "rec_loop_invar Vl va (v, p, cS)"
    hence "(v,va) \<in> (?E)\<^sup>*"
      unfolding rec_loop_invar_def
      using CONN rtrancl_mono[OF E_SS]
      by auto
  } note CLOSE2 = this

  {
    fix "pr" vd pl va v0
    assume "rec_loop_invar Vl va (vd, [], {0..<num_acc})" "va \<in> Vl" "v0 \<in> V0"
      "path E v0 pr va" "pl \<noteq> []" "path ?E vd pl va"
    hence "is_lasso_prpl (pr, pl)"
      unfolding is_lasso_prpl_def is_lasso_prpl_pre_def rec_loop_invar_def
      by (auto simp: neq_Nil_conv path_simps
        dest!: path_mono[of "?E" E, simplified]) []
  } note INV_POST1 = this

  {
    fix va v p p' "pr" v0
    assume INV: "rec_loop_invar Vl va (v,p,{0..<num_acc})" 
      and 1: "p\<noteq>[]" "path ?E v p' va"
      and PR: "v0\<in>V0" "path E v0 pr va"

    from INV have "\<forall>i<num_acc. \<exists>q\<in>insert v (set p). i \<in> acc q"
      unfolding rec_loop_invar_def
      by auto
    moreover from INV 1 have "insert v (set p) \<subseteq> set p \<union> set p'"
      unfolding rec_loop_invar_def
      apply (cases p, simp)
      apply (cases p')
      apply (auto simp: path_simps)
      done
    ultimately have ACC: "\<forall>i<num_acc. \<exists>q\<in>set p \<union> set p'. i \<in> acc q" by blast
    
    from INV 1 have PL: "path E va (p @ p') va"
      by (auto simp: rec_loop_invar_def path_simps 
        dest!: path_mono[of "?E" E, simplified]) []

    have "is_lasso_prpl (pr,p@p')"
      unfolding is_lasso_prpl_def is_lasso_prpl_pre_def
      apply (clarsimp simp: ACC)
      using PR PL \<open>p\<noteq>[]\<close> by auto
  } note INV_POST2 = this

  show ?thesis
    unfolding reconstruct_lasso_def
    apply (refine_rcg 
      WF
      order_trans[OF reconstruct_reach_correct]
      order_trans[OF find_path_ex_rule]
      order_trans[OF find_path1_ex_rule]
      refine_vcg 
    )

    apply (vc_solve 
      del: subsetI
      solve: ASSERT1 INV_PRES asm_rl VAR CLOSE1 CLOSE2 INV_POST1 INV_POST2
      simp: INVAR_INITIAL FIN1 CEC)
    done
qed

definition find_lasso where "find_lasso \<equiv> do {
  ce \<leftarrow> find_ce_spec;
  case ce of 
    None \<Rightarrow> RETURN None
  | Some (Vr,Vl) \<Rightarrow> do {
      l \<leftarrow> reconstruct_lasso Vr Vl;
      RETURN (Some l)
    }
}"

lemma (in igb_fr_graph) find_lasso_correct: "find_lasso \<le> find_lasso_spec"
  unfolding find_lasso_spec_def find_lasso_def find_ce_spec_def
  apply (refine_rcg refine_vcg order_trans[OF reconstruct_lasso_correct])
  apply auto
  done

end

end
