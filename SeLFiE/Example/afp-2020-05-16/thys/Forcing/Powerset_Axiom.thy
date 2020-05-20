section\<open>The Powerset Axiom in $M[G]$\<close>
theory Powerset_Axiom
  imports Renaming_Auto Separation_Axiom Pairing_Axiom Union_Axiom
begin

simple_rename "perm_pow" src "[ss,p,l,o,fs,\<chi>]" tgt "[fs,ss,sp,p,l,o,\<chi>]"

lemma Collect_inter_Transset:
  assumes
    "Transset(M)" "b \<in> M"
  shows
    "{x\<in>b . P(x)} = {x\<in>b . P(x)} \<inter> M"
  using assms unfolding Transset_def
  by (auto)

context G_generic  begin

lemma name_components_in_M:
  assumes "<\<sigma>,p>\<in>\<theta>" "\<theta> \<in> M"
  shows   "\<sigma>\<in>M" "p\<in>M"
proof -
  from assms obtain a where
    "\<sigma> \<in> a" "p \<in> a" "a\<in><\<sigma>,p>"
    unfolding Pair_def by auto
  moreover from assms
  have "<\<sigma>,p>\<in>M"
    using transitivity by simp
  moreover from calculation
  have "a\<in>M"
    using transitivity by simp
  ultimately
  show "\<sigma>\<in>M" "p\<in>M"
    using transitivity by simp_all
qed

lemma sats_fst_snd_in_M:
  assumes
    "A\<in>M" "B\<in>M" "\<phi> \<in> formula" "p\<in>M" "l\<in>M" "o\<in>M" "\<chi>\<in>M"
    "arity(\<phi>) \<le> 6"
  shows
    "{sq \<in>A\<times>B . sats(M,\<phi>,[snd(sq),p,l,o,fst(sq),\<chi>])} \<in> M"
    (is "?\<theta> \<in> M")
proof -
  have "6\<in>nat" "7\<in>nat" by simp_all
  let ?\<phi>' = "ren(\<phi>)`6`7`perm_pow_fn"
  from \<open>A\<in>M\<close> \<open>B\<in>M\<close> have
    "A\<times>B \<in> M"
    using cartprod_closed by simp
  from \<open>arity(\<phi>) \<le> 6\<close> \<open>\<phi>\<in> formula\<close> \<open>6\<in>_\<close> \<open>7\<in>_\<close>
  have "?\<phi>' \<in> formula" "arity(?\<phi>')\<le>7"
    unfolding perm_pow_fn_def
    using  perm_pow_thm  arity_ren ren_tc Nil_type
    by auto
  with \<open>?\<phi>' \<in> formula\<close>
  have 1: "arity(Exists(Exists(And(pair_fm(0,1,2),?\<phi>'))))\<le>5"     (is "arity(?\<psi>)\<le>5")
    unfolding pair_fm_def upair_fm_def
    using nat_simp_union pred_le arity_type by auto
  {
    fix sp
    note \<open>A\<times>B \<in> M\<close>
    moreover
    assume "sp \<in> A\<times>B"
    moreover from calculation
    have "fst(sp) \<in> A" "snd(sp) \<in> B"
      using fst_type snd_type by simp_all
    ultimately
    have "sp \<in> M" "fst(sp) \<in> M" "snd(sp) \<in> M"
      using  \<open>A\<in>M\<close> \<open>B\<in>M\<close> transitivity
      by simp_all
    note inM = \<open>A\<in>M\<close> \<open>B\<in>M\<close> \<open>p\<in>M\<close> \<open>l\<in>M\<close> \<open>o\<in>M\<close> \<open>\<chi>\<in>M\<close>
      \<open>sp\<in>M\<close> \<open>fst(sp)\<in>M\<close> \<open>snd(sp)\<in>M\<close>
    with 1 \<open>sp \<in> M\<close> \<open>?\<phi>' \<in> formula\<close>
    have "M, [sp,p,l,o,\<chi>]@[p] \<Turnstile> ?\<psi> \<longleftrightarrow> M,[sp,p,l,o,\<chi>] \<Turnstile> ?\<psi>" (is "M,?env0@ _\<Turnstile>_ \<longleftrightarrow> _")
      using arity_sats_iff[of ?\<psi> "[p]" M ?env0] by auto
    also from inM \<open>sp \<in> A\<times>B\<close>
    have "... \<longleftrightarrow> sats(M,?\<phi>',[fst(sp),snd(sp),sp,p,l,o,\<chi>])"
      by auto
    also from inM \<open>\<phi> \<in> formula\<close> \<open>arity(\<phi>) \<le> 6\<close>
    have "... \<longleftrightarrow> sats(M,\<phi>,[snd(sp),p,l,o,fst(sp),\<chi>])"
      (is "sats(_,_,?env1) \<longleftrightarrow> sats(_,_,?env2)")
      using sats_iff_sats_ren[of \<phi> 6 7 ?env2 M ?env1 perm_pow_fn] perm_pow_thm
      unfolding perm_pow_fn_def by simp
    finally
    have "sats(M,?\<psi>,[sp,p,l,o,\<chi>,p]) \<longleftrightarrow> sats(M,\<phi>,[snd(sp),p,l,o,fst(sp),\<chi>])"
      by simp
  }
  then have
    "?\<theta> = {sp\<in>A\<times>B . sats(M,?\<psi>,[sp,p,l,o,\<chi>,p])}"
    by auto
  also from assms \<open>A\<times>B\<in>M\<close> have
    " ... \<in> M"
  proof -
    from 1
    have "arity(?\<psi>) \<le> 6"
      using leI by simp
    moreover from \<open>?\<phi>' \<in> formula\<close>
    have "?\<psi> \<in> formula"
      by simp
    moreover note assms \<open>A\<times>B\<in>M\<close>
    ultimately 
    show "{x \<in> A\<times>B . sats(M, ?\<psi>, [x, p, l, o, \<chi>, p])} \<in> M"
      using separation_ax separation_iff
      by simp
  qed
  finally show ?thesis .
qed

lemma Pow_inter_MG:
  assumes
    "a\<in>M[G]"
  shows
    "Pow(a) \<inter> M[G] \<in> M[G]"
proof -
  from assms obtain \<tau> where
    "\<tau> \<in> M" "val(G, \<tau>) = a"
    using GenExtD by auto
  let ?Q="Pow(domain(\<tau>)\<times>P) \<inter> M"
  from \<open>\<tau>\<in>M\<close> 
  have "domain(\<tau>)\<times>P \<in> M" "domain(\<tau>) \<in> M"
    using domain_closed cartprod_closed P_in_M
    by simp_all
  then 
  have "?Q \<in> M"
  proof -
    from power_ax \<open>domain(\<tau>)\<times>P \<in> M\<close> obtain Q where
      "powerset(##M,domain(\<tau>)\<times>P,Q)" "Q \<in> M"
      unfolding power_ax_def by auto
    moreover from calculation 
    have "z\<in>Q \<Longrightarrow> z\<in>M" for z
      using transitivity by blast
    ultimately
    have "Q = {a\<in>Pow(domain(\<tau>)\<times>P) . a\<in>M}"
      using \<open>domain(\<tau>)\<times>P \<in> M\<close> powerset_abs[of "domain(\<tau>)\<times>P" Q]
      by (simp flip: setclass_iff)
    also 
    have " ... = ?Q"
      by auto
    finally 
    show ?thesis using \<open>Q\<in>M\<close> by simp
  qed
  let
    ?\<pi>="?Q\<times>{one}"
  let
    ?b="val(G,?\<pi>)"
  from \<open>?Q\<in>M\<close> 
  have "?\<pi>\<in>M"
    using one_in_P P_in_M transitivity
    by (simp flip: setclass_iff)
  from \<open>?\<pi>\<in>M\<close> 
  have "?b \<in> M[G]"
    using GenExtI by simp
  have "Pow(a) \<inter> M[G] \<subseteq> ?b"
  proof
    fix c
    assume "c \<in> Pow(a) \<inter> M[G]"
    then obtain \<chi> where
      "c\<in>M[G]" "\<chi> \<in> M" "val(G,\<chi>) = c"
      using GenExtD by auto
    let ?\<theta>="{sp \<in>domain(\<tau>)\<times>P . snd(sp) \<tturnstile> (Member(0,1)) [fst(sp),\<chi>] }"
    have "arity(forces(Member(0,1))) = 6"
      using arity_forces_at by auto
    with \<open>domain(\<tau>) \<in> M\<close> \<open>\<chi> \<in> M\<close> 
    have "?\<theta> \<in> M"
      using P_in_M one_in_M leq_in_M sats_fst_snd_in_M
      by simp
    then 
    have "?\<theta> \<in> ?Q"
      by auto
    then 
    have "val(G,?\<theta>) \<in> ?b"
      using one_in_G one_in_P generic val_of_elem [of ?\<theta> one ?\<pi> G]
      by auto
    have "val(G,?\<theta>) = c"
    proof(intro equalityI subsetI)
      fix x
      assume "x \<in> val(G,?\<theta>)"
      then obtain \<sigma> p where
        1: "<\<sigma>,p>\<in>?\<theta>" "p\<in>G" "val(G,\<sigma>) =  x"
        using elem_of_val_pair
        by blast
      moreover from \<open><\<sigma>,p>\<in>?\<theta>\<close> \<open>?\<theta> \<in> M\<close>
      have "\<sigma>\<in>M"
        using name_components_in_M[of _ _ ?\<theta>] by auto
      moreover from 1 
      have "(p \<tturnstile> (Member(0,1)) [\<sigma>,\<chi>])" "p\<in>P"
        by simp_all
      moreover 
      note \<open>val(G,\<chi>) = c\<close>
      ultimately 
      have "sats(M[G],Member(0,1),[x,c])"
        using \<open>\<chi> \<in> M\<close> generic definition_of_forcing nat_simp_union
        by auto
      moreover 
      have "x\<in>M[G]"
        using \<open>val(G,\<sigma>) =  x\<close> \<open>\<sigma>\<in>M\<close>  \<open>\<chi>\<in>M\<close> GenExtI by blast
      ultimately 
      show "x\<in>c"
        using \<open>c\<in>M[G]\<close> by simp
    next
      fix x
      assume "x \<in> c"
      with \<open>c \<in> Pow(a) \<inter> M[G]\<close> 
      have "x \<in> a" "c\<in>M[G]" "x\<in>M[G]"
        using transitivity_MG
        by auto
      with \<open>val(G, \<tau>) = a\<close> 
      obtain \<sigma> where
        "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) =  x"
        using elem_of_val
        by blast
      moreover note \<open>x\<in>c\<close> \<open>val(G,\<chi>) = c\<close>
      moreover from calculation 
      have "val(G,\<sigma>) \<in> val(G,\<chi>)"
        by simp
      moreover note \<open>c\<in>M[G]\<close> \<open>x\<in>M[G]\<close>
      moreover from calculation 
      have "sats(M[G],Member(0,1),[x,c])"
        by simp
      moreover 
      have "Member(0,1)\<in>formula" by simp
      moreover 
      have "\<sigma>\<in>M"
      proof -
        from \<open>\<sigma>\<in>domain(\<tau>)\<close> 
        obtain p where "<\<sigma>,p> \<in> \<tau>"
          by auto
        with \<open>\<tau>\<in>M\<close> 
        show ?thesis
          using name_components_in_M by blast
      qed
      moreover note \<open>\<chi> \<in> M\<close>
      ultimately 
      obtain p where "p\<in>G" "(p \<tturnstile> Member(0,1) [\<sigma>,\<chi>])"
        using generic truth_lemma[of "Member(0,1)" "G" "[\<sigma>,\<chi>]" ] nat_simp_union
        by auto
      moreover from \<open>p\<in>G\<close> 
      have "p\<in>P"
        using generic unfolding M_generic_def filter_def by blast
      ultimately
      have "<\<sigma>,p>\<in>?\<theta>"
        using \<open>\<sigma>\<in>domain(\<tau>)\<close> by simp
      with \<open>val(G,\<sigma>) =  x\<close> \<open>p\<in>G\<close> 
      show "x\<in>val(G,?\<theta>)"
        using val_of_elem [of _ _ "?\<theta>"] by auto
    qed
    with \<open>val(G,?\<theta>) \<in> ?b\<close> 
    show "c\<in>?b" by simp
  qed
  then 
  have "Pow(a) \<inter> M[G] = {x\<in>?b . x\<subseteq>a & x\<in>M[G]}"
    by auto
  also from \<open>a\<in>M[G]\<close> 
  have " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a]) & x\<in>M[G]}"
    using Transset_MG by force
  also 
  have " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])} \<inter> M[G]"
    by auto
  also from \<open>?b\<in>M[G]\<close> 
  have " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])}"
    using Collect_inter_Transset Transset_MG
    by simp
  also from \<open>?b\<in>M[G]\<close> \<open>a\<in>M[G]\<close>
  have " ... \<in> M[G]"
    using Collect_sats_in_MG GenExtI nat_simp_union by simp
  finally show ?thesis .
qed
end (* context: G_generic *)


context G_generic begin

interpretation mgtriv: M_trivial "##M[G]"
  using generic Union_MG pairing_in_MG zero_in_MG transitivity_MG
  unfolding M_trivial_def M_trans_def M_trivial_axioms_def by (simp; blast)


theorem power_in_MG : "power_ax(##(M[G]))"
  unfolding power_ax_def
proof (intro rallI, simp only:setclass_iff rex_setclass_is_bex)
  (* After simplification, we have to show that for every
     a\<in>M[G] there exists some x\<in>M[G] with powerset(##M[G],a,x)
  *)
  fix a
  assume "a \<in> M[G]"
  then
  have "(##M[G])(a)" by simp
  have "{x\<in>Pow(a) . x \<in> M[G]} = Pow(a) \<inter> M[G]"
    by auto
  also from \<open>a\<in>M[G]\<close> 
  have " ... \<in> M[G]"
    using Pow_inter_MG by simp
  finally 
  have "{x\<in>Pow(a) . x \<in> M[G]} \<in> M[G]" .
  moreover from \<open>a\<in>M[G]\<close> \<open>{x\<in>Pow(a) . x \<in> M[G]} \<in> _\<close> 
  have "powerset(##M[G], a, {x\<in>Pow(a) . x \<in> M[G]})"
    using mgtriv.powerset_abs[OF \<open>(##M[G])(a)\<close>]
    by simp
  ultimately 
  show "\<exists>x\<in>M[G] . powerset(##M[G], a, x)"
    by auto
qed
end (* context: G_generic *)
end