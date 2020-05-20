section\<open>The Axiom of Replacement in $M[G]$\<close>
theory Replacement_Axiom
  imports
    Least Relative_Univ Separation_Axiom Renaming_Auto
begin

rename "renrep1" src "[p,P,leq,o,\<rho>,\<tau>]" tgt "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o]"

definition renrep_fn :: "i \<Rightarrow> i" where
  "renrep_fn(env) \<equiv> sum(renrep1_fn,id(length(env)),6,8,length(env))"

definition
  renrep :: "[i,i] \<Rightarrow> i" where
  "renrep(\<phi>,env) = ren(\<phi>)`(6#+length(env))`(8#+length(env))`renrep_fn(env)"

lemma renrep_type [TC]:
  assumes "\<phi>\<in>formula" "env \<in> list(M)"
  shows "renrep(\<phi>,env) \<in> formula"
  unfolding renrep_def renrep_fn_def renrep1_fn_def
  using assms renrep1_thm(1) ren_tc
  by simp

lemma arity_renrep:
  assumes  "\<phi>\<in>formula" "arity(\<phi>)\<le> 6#+length(env)" "env \<in> list(M)"
  shows "arity(renrep(\<phi>,env)) \<le> 8#+length(env)"
  unfolding  renrep_def renrep_fn_def renrep1_fn_def
  using assms renrep1_thm(1) arity_ren
  by simp

lemma renrep_sats :
  assumes  "arity(\<phi>) \<le> 6 #+ length(env)"
          "[P,leq,o,p,\<rho>,\<tau>] @ env \<in> list(M)"
    "V \<in> M" "\<alpha> \<in> M"
    "\<phi>\<in>formula"
  shows "sats(M, \<phi>, [p,P,leq,o,\<rho>,\<tau>] @ env) \<longleftrightarrow> sats(M, renrep(\<phi>,env), [V,\<tau>,\<rho>,p,\<alpha>,P,leq,o] @ env)"
  unfolding  renrep_def renrep_fn_def renrep1_fn_def
  by (rule sats_iff_sats_ren,insert assms, auto simp add:renrep1_thm(1)[of _ M,simplified]
        renrep1_thm(2)[simplified,where p=p and \<alpha>=\<alpha>])

rename "renpbdy1" src "[\<rho>,p,\<alpha>,P,leq,o]" tgt "[\<rho>,p,x,\<alpha>,P,leq,o]"

definition renpbdy_fn :: "i \<Rightarrow> i" where
  "renpbdy_fn(env) \<equiv> sum(renpbdy1_fn,id(length(env)),6,7,length(env))"

definition
  renpbdy :: "[i,i] \<Rightarrow> i" where
  "renpbdy(\<phi>,env) = ren(\<phi>)`(6#+length(env))`(7#+length(env))`renpbdy_fn(env)"


lemma
  renpbdy_type [TC]: "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> renpbdy(\<phi>,env) \<in> formula"
  unfolding renpbdy_def renpbdy_fn_def renpbdy1_fn_def
  using  renpbdy1_thm(1) ren_tc
  by simp

lemma  arity_renpbdy: "\<phi>\<in>formula \<Longrightarrow> arity(\<phi>) \<le> 6 #+ length(env) \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(renpbdy(\<phi>,env)) \<le> 7 #+ length(env)"
  unfolding renpbdy_def renpbdy_fn_def renpbdy1_fn_def
  using  renpbdy1_thm(1) arity_ren
  by simp

lemma
  sats_renpbdy: "arity(\<phi>) \<le> 6 #+ length(nenv) \<Longrightarrow> [\<rho>,p,x,\<alpha>,P,leq,o,\<pi>] @ nenv \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
       sats(M, \<phi>, [\<rho>,p,\<alpha>,P,leq,o] @ nenv) \<longleftrightarrow> sats(M, renpbdy(\<phi>,nenv), [\<rho>,p,x,\<alpha>,P,leq,o] @ nenv)"
  unfolding renpbdy_def renpbdy_fn_def renpbdy1_fn_def
  by (rule sats_iff_sats_ren,auto simp add: renpbdy1_thm(1)[of _ M,simplified]
                                            renpbdy1_thm(2)[simplified,where \<alpha>=\<alpha> and x=x])


rename "renbody1" src "[x,\<alpha>,P,leq,o]" tgt "[\<alpha>,x,m,P,leq,o]"

definition renbody_fn :: "i \<Rightarrow> i" where
  "renbody_fn(env) \<equiv> sum(renbody1_fn,id(length(env)),5,6,length(env))"

definition
  renbody :: "[i,i] \<Rightarrow> i" where
  "renbody(\<phi>,env) = ren(\<phi>)`(5#+length(env))`(6#+length(env))`renbody_fn(env)"

lemma
  renbody_type [TC]: "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> renbody(\<phi>,env) \<in> formula"
  unfolding renbody_def renbody_fn_def renbody1_fn_def
  using  renbody1_thm(1) ren_tc
  by simp

lemma  arity_renbody: "\<phi>\<in>formula \<Longrightarrow> arity(\<phi>) \<le> 5 #+ length(env) \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
  arity(renbody(\<phi>,env)) \<le> 6 #+ length(env)"
  unfolding renbody_def renbody_fn_def renbody1_fn_def
  using  renbody1_thm(1) arity_ren
  by simp

lemma
  sats_renbody: "arity(\<phi>) \<le> 5 #+ length(nenv) \<Longrightarrow> [\<alpha>,x,m,P,leq,o] @ nenv \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
       sats(M, \<phi>, [x,\<alpha>,P,leq,o] @ nenv) \<longleftrightarrow> sats(M, renbody(\<phi>,nenv), [\<alpha>,x,m,P,leq,o] @ nenv)"
  unfolding renbody_def renbody_fn_def renbody1_fn_def
  by (rule sats_iff_sats_ren, auto simp add:renbody1_thm(1)[of _ M,simplified]
                                            renbody1_thm(2)[where \<alpha>=\<alpha> and m=m,simplified])

context G_generic
begin

lemma pow_inter_M:
  assumes
    "x\<in>M" "y\<in>M"
  shows
    "powerset(##M,x,y) \<longleftrightarrow> y = Pow(x) \<inter> M"
  using assms by auto


schematic_goal sats_prebody_fm_auto:
  assumes
    "\<phi>\<in>formula" "[P,leq,one,p,\<rho>,\<pi>] @ nenv \<in>list(M)"  "\<alpha>\<in>M" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "(\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> sats(M,forces(\<phi>),[p,P,leq,one,\<rho>,\<tau>] @ nenv))
   \<longleftrightarrow> sats(M,?prebody_fm,[\<rho>,p,\<alpha>,P,leq,one] @ nenv)"
  apply (insert assms; (rule sep_rules is_Vset_iff_sats[OF _ _ _ _ _ nonempty[simplified]] | simp))
   apply (rule sep_rules is_Vset_iff_sats is_Vset_iff_sats[OF _ _ _ _ _ nonempty[simplified]] | simp)+
        apply (rule nonempty[simplified])
       apply (simp_all)
    apply (rule length_type[THEN nat_into_Ord], blast)+
  apply ((rule sep_rules | simp))
    apply ((rule sep_rules | simp))
      apply ((rule sep_rules | simp))
       apply ((rule sep_rules | simp))
      apply ((rule sep_rules | simp))
     apply ((rule sep_rules | simp))
    apply ((rule sep_rules | simp))
   apply (rule renrep_sats[simplified])
       apply (insert assms)
       apply(auto simp add: renrep_type definability)
proof -
  from assms
  have "nenv\<in>list(M)" by simp
  with \<open>arity(\<phi>)\<le>_\<close> \<open>\<phi>\<in>_\<close>
  show "arity(forces(\<phi>)) \<le> succ(succ(succ(succ(succ(succ(length(nenv)))))))"
    using arity_forces_le by simp
qed

(* The formula synthesized above *)
synthesize_notc "prebody_fm" from_schematic sats_prebody_fm_auto

lemma prebody_fm_type [TC]:
  assumes "\<phi>\<in>formula"
    "env \<in> list(M)"
  shows "prebody_fm(\<phi>,env)\<in>formula"
proof -
  from \<open>\<phi>\<in>formula\<close>
  have "forces(\<phi>)\<in>formula" by simp
  then
  have "renrep(forces(\<phi>),env)\<in>formula"
    using \<open>env\<in>list(M)\<close> by simp
  then show ?thesis unfolding prebody_fm_def by simp
qed

lemmas new_fm_defs = fm_defs is_transrec_fm_def is_eclose_fm_def mem_eclose_fm_def
  finite_ordinal_fm_def is_wfrec_fm_def  Memrel_fm_def eclose_n_fm_def is_recfun_fm_def is_iterates_fm_def
  iterates_MH_fm_def is_nat_case_fm_def quasinat_fm_def pre_image_fm_def restriction_fm_def

lemma sats_prebody_fm:
  assumes
    "[P,leq,one,p,\<rho>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "\<alpha>\<in>M" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "sats(M,prebody_fm(\<phi>,nenv),[\<rho>,p,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow>
     (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> sats(M,forces(\<phi>),[p,P,leq,one,\<rho>,\<tau>] @ nenv))"
  unfolding prebody_fm_def using assms sats_prebody_fm_auto by force


lemma arity_prebody_fm:
  assumes
    "\<phi>\<in>formula" "\<alpha>\<in>M" "env \<in> list(M)" "arity(\<phi>) \<le> 2 #+ length(env)"
  shows
    "arity(prebody_fm(\<phi>,env))\<le>6 #+ length(env)"
  unfolding prebody_fm_def is_HVfrom_fm_def is_powapply_fm_def
  using assms new_fm_defs nat_simp_union
    arity_renrep[of "forces(\<phi>)"] arity_forces_le[simplified] pred_le by auto


definition
  body_fm' :: "[i,i]\<Rightarrow>i" where
  "body_fm'(\<phi>,env) \<equiv> Exists(Exists(And(pair_fm(0,1,2),renpbdy(prebody_fm(\<phi>,env),env))))"

lemma body_fm'_type[TC]: "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> body_fm'(\<phi>,env)\<in>formula"
  unfolding body_fm'_def using prebody_fm_type
  by simp

lemma arity_body_fm':
  assumes
    "\<phi>\<in>formula" "\<alpha>\<in>M" "env\<in>list(M)" "arity(\<phi>) \<le> 2 #+ length(env)"
  shows
    "arity(body_fm'(\<phi>,env))\<le>5  #+ length(env)"
  unfolding body_fm'_def
  using assms new_fm_defs nat_simp_union arity_prebody_fm pred_le  arity_renpbdy[of "prebody_fm(\<phi>,env)"]
  by auto

lemma sats_body_fm':
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "x\<in>M" "[\<alpha>,P,leq,one,p,\<rho>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "sats(M,body_fm'(\<phi>,nenv),[x,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow>
     sats(M,renpbdy(prebody_fm(\<phi>,nenv),nenv),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv)"
  using assms fst_snd_closed[OF \<open>x\<in>M\<close>] unfolding body_fm'_def
  by (auto)

definition
  body_fm :: "[i,i]\<Rightarrow>i" where
  "body_fm(\<phi>,env) \<equiv> renbody(body_fm'(\<phi>,env),env)"

lemma body_fm_type [TC]: "env\<in>list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>  body_fm(\<phi>,env)\<in>formula"
  unfolding body_fm_def by simp

lemma sats_body_fm:
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "[\<alpha>,x,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "sats(M,body_fm(\<phi>,nenv),[\<alpha>,x,m,P,leq,one] @ nenv) \<longleftrightarrow>
     sats(M,renpbdy(prebody_fm(\<phi>,nenv),nenv),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv)"
  using assms sats_body_fm' sats_renbody[OF _ assms(2), symmetric] arity_body_fm'
  unfolding body_fm_def
  by auto

lemma sats_renpbdy_prebody_fm:
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "x\<in>M" "[\<alpha>,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "sats(M,renpbdy(prebody_fm(\<phi>,nenv),nenv),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow>
     sats(M,prebody_fm(\<phi>,nenv),[fst(x),snd(x),\<alpha>,P,leq,one] @ nenv)"
  using assms fst_snd_closed[OF \<open>x\<in>M\<close>]
    sats_renpbdy[OF arity_prebody_fm _ prebody_fm_type, of concl:M, symmetric]
  by force

lemma body_lemma:
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "x\<in>M" "[x,\<alpha>,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows
    "sats(M,body_fm(\<phi>,nenv),[\<alpha>,x,m,P,leq,one] @ nenv) \<longleftrightarrow>
  (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a),\<alpha>,V) \<and> \<tau> \<in> V \<and> (snd(x) \<tturnstile> \<phi> ([fst(x),\<tau>]@nenv)))"
  using assms sats_body_fm[of x \<alpha> m nenv] sats_renpbdy_prebody_fm[of x \<alpha>]
    sats_prebody_fm[of "snd(x)" "fst(x)"] fst_snd_closed[OF \<open>x\<in>M\<close>]
  by (simp, simp flip: setclass_iff,simp)

lemma Replace_sats_in_MG:
  assumes
    "c\<in>M[G]" "env \<in> list(M[G])"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 #+ length(env)"
    "univalent(##M[G], c, \<lambda>x v. (M[G] , [x,v]@env \<Turnstile> \<phi>) )"
  shows
    "{v. x\<in>c, v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)} \<in> M[G]"
proof -
  let ?R = "\<lambda> x v . v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)"
  from \<open>c\<in>M[G]\<close>
  obtain \<pi>' where "val(G, \<pi>') = c" "\<pi>' \<in> M"
    using GenExt_def by auto
  then
  have "domain(\<pi>')\<times>P\<in>M" (is "?\<pi>\<in>M")
    using cartprod_closed P_in_M domain_closed by simp
  from \<open>val(G, \<pi>') = c\<close>
  have "c \<subseteq> val(G,?\<pi>)"
    using def_val[of G ?\<pi>] one_in_P one_in_G[OF generic] elem_of_val
      domain_of_prod[OF one_in_P, of "domain(\<pi>')"] by force
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" by simp
  define f where "f(\<rho>p) \<equiv> \<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<tau> \<in> Vset(\<alpha>) \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv)))" (is "_ \<equiv> \<mu> \<alpha>. ?P(\<rho>p,\<alpha>)") for \<rho>p
  have "f(\<rho>p) = (\<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))))" (is "_ = (\<mu> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>))") for \<rho>p
    unfolding f_def using Vset_abs Vset_closed Ord_Least_cong[of "?P(\<rho>p)" "\<lambda> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)"]
    by (simp, simp del:setclass_iff)
  moreover
  have "f(\<rho>p) \<in> M" for \<rho>p
    unfolding f_def using Least_closed[of "?P(\<rho>p)"] by simp
  ultimately
  have 1:"least(##M,\<lambda>\<alpha>. ?Q(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    using least_abs[of "\<lambda>\<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)" "f(\<rho>p)"] least_conj
    by (simp flip: setclass_iff)
  have "Ord(f(\<rho>p))" for \<rho>p unfolding f_def by simp
  define QQ where "QQ\<equiv>?Q"
  from 1
  have "least(##M,\<lambda>\<alpha>. QQ(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    unfolding QQ_def .
  from \<open>arity(\<phi>) \<le> _\<close> \<open>length(nenv) = _\<close>
  have "arity(\<phi>) \<le> 2 #+ length(nenv)"
    by simp
  moreover
  note assms \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  moreover
  have "\<rho>p\<in>?\<pi> \<Longrightarrow> \<exists>t p. \<rho>p=\<langle>t,p\<rangle>" for \<rho>p
    by auto
  ultimately
  have body:"M , [\<alpha>,\<rho>p,m,P,leq,one] @ nenv \<Turnstile> body_fm(\<phi>,nenv) \<longleftrightarrow> ?Q(\<rho>p,\<alpha>)"
    if "\<rho>p\<in>?\<pi>" "\<rho>p\<in>M" "m\<in>M" "\<alpha>\<in>M" for \<alpha> \<rho>p m
    using that P_in_M leq_in_M one_in_M body_lemma[of \<rho>p \<alpha> m nenv \<phi>] by simp
  let ?f_fm="least_fm(body_fm(\<phi>,nenv),1)"
  {
    fix \<rho>p m
    assume asm: "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M"
    note inM = this P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close>
    with body
    have body':"\<And>\<alpha>. \<alpha> \<in> M \<Longrightarrow> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a), \<alpha>, V) \<and> \<tau> \<in> V \<and>
          (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))) \<longleftrightarrow>
          M, Cons(\<alpha>, [\<rho>p, m, P, leq, one] @ nenv) \<Turnstile> body_fm(\<phi>,nenv)" by simp
    from inM
    have "M , [\<rho>p,m,P,leq,one] @ nenv \<Turnstile> ?f_fm \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
      using sats_least_fm[OF body', of 1] unfolding QQ_def
      by (simp, simp flip: setclass_iff)
  }
  then
  have "M, [\<rho>p,m,P,leq,one] @ nenv \<Turnstile> ?f_fm \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
    if "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M" for \<rho>p m using that by simp
  then
  have "univalent(##M, ?\<pi>, \<lambda>\<rho>p m. M , [\<rho>p,m] @ ([P,leq,one] @ nenv) \<Turnstile> ?f_fm)"
    unfolding univalent_def by (auto intro:unique_least)
  moreover from \<open>length(_) = _\<close> \<open>env \<in> _\<close>
  have "length([P,leq,one] @ nenv) = 3 #+ length(env)" by simp
  moreover from \<open>arity(_) \<le> 2 #+ length(nenv)\<close>
    \<open>length(_) = length(_)\<close>[symmetric] \<open>nenv\<in>_\<close> \<open>\<phi>\<in>_\<close>
  have "arity(?f_fm) \<le> 5 #+ length(env)"
    unfolding body_fm_def  new_fm_defs least_fm_def
    using arity_forces arity_renrep arity_renbody arity_body_fm' nonempty
    by (simp add: pred_Un Un_assoc, simp add: Un_assoc[symmetric] nat_union_abs1 pred_Un)
      (auto simp add: nat_simp_union, rule pred_le, auto intro:leI)
  moreover from \<open>\<phi>\<in>formula\<close> \<open>nenv\<in>list(M)\<close>
  have "?f_fm\<in>formula" by simp
  moreover
  note inM = P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  ultimately
  obtain Y where "Y\<in>M"
    "\<forall>m\<in>M. m \<in> Y \<longleftrightarrow> (\<exists>\<rho>p\<in>M. \<rho>p \<in> ?\<pi> \<and> M, [\<rho>p,m] @ ([P,leq,one] @ nenv) \<Turnstile> ?f_fm)"
    using replacement_ax[of ?f_fm "[P,leq,one] @ nenv"]
    unfolding strong_replacement_def by auto
  with \<open>least(_,QQ(_),f(_))\<close> \<open>f(_) \<in> M\<close> \<open>?\<pi>\<in>M\<close>
    \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> M,_ \<Turnstile> ?f_fm \<longleftrightarrow> least(_,_,_)\<close>
  have "f(\<rho>p)\<in>Y" if "\<rho>p\<in>?\<pi>" for \<rho>p
    using that transitivity[OF _ \<open>?\<pi>\<in>M\<close>]
    by (clarsimp, rule_tac x="\<langle>x,y\<rangle>" in bexI, auto)
  moreover
  have "{y\<in>Y. Ord(y)} \<in> M"
    using \<open>Y\<in>M\<close> separation_ax sats_ordinal_fm trans_M
      separation_cong[of "##M" "\<lambda>y. sats(M,ordinal_fm(0),[y])" "Ord"]
      separation_closed by simp
  then
  have "\<Union> {y\<in>Y. Ord(y)} \<in> M" (is "?sup \<in> M")
    using Union_closed by simp
  then
  have "{x\<in>Vset(?sup). x \<in> M} \<in> M"
    using Vset_closed by simp
  moreover
  have "{one} \<in> M"
    using one_in_M singletonM by simp
  ultimately
  have "{x\<in>Vset(?sup). x \<in> M} \<times> {one} \<in> M" (is "?big_name \<in> M")
    using cartprod_closed by simp
  then
  have "val(G,?big_name) \<in> M[G]"
    by (blast intro:GenExtI)
  {
    fix v x
    assume "x\<in>c"
    moreover
    note \<open>val(G,\<pi>')=c\<close> \<open>\<pi>'\<in>M\<close>
    moreover
    from calculation
    obtain \<rho> p where "\<langle>\<rho>,p\<rangle>\<in>\<pi>'"  "val(G,\<rho>) = x" "p\<in>G" "\<rho>\<in>M"
      using elem_of_val_pair'[of \<pi>' x G] by blast
    moreover
    assume "v\<in>M[G]"
    then
    obtain \<sigma> where "val(G,\<sigma>) = v" "\<sigma>\<in>M"
      using GenExtD by auto
    moreover
    assume "sats(M[G], \<phi>, [x,v] @ env)"
    moreover
    note \<open>\<phi>\<in>_\<close> \<open>nenv\<in>_\<close> \<open>env = _\<close> \<open>arity(\<phi>)\<le> 2 #+ length(env)\<close>
    ultimately
    obtain q where "q\<in>G" "q \<tturnstile> \<phi> ([\<rho>,\<sigma>]@nenv)"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> generic, symmetric, of "[\<rho>,\<sigma>] @ nenv"]
      by auto
    with \<open>\<langle>\<rho>,p\<rangle>\<in>\<pi>'\<close> \<open>\<langle>\<rho>,q\<rangle>\<in>?\<pi> \<Longrightarrow> f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "f(\<langle>\<rho>,q\<rangle>)\<in>Y"
      using generic unfolding M_generic_def filter_def by blast
    let ?\<alpha>="succ(rank(\<sigma>))"
    note \<open>\<sigma>\<in>M\<close>
    moreover from this
    have "?\<alpha> \<in> M"
      using rank_closed cons_closed by (simp flip: setclass_iff)
    moreover
    have "\<sigma> \<in> Vset(?\<alpha>)"
      using Vset_Ord_rank_iff by auto
    moreover
    note \<open>q \<tturnstile> \<phi> ([\<rho>,\<sigma>] @ nenv)\<close>
    ultimately
    have "?P(\<langle>\<rho>,q\<rangle>,?\<alpha>)" by (auto simp del: Vset_rank_iff)
    moreover
    have "(\<mu> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)) = f(\<langle>\<rho>,q\<rangle>)"
      unfolding f_def by simp
    ultimately
    obtain \<tau> where "\<tau>\<in>M" "\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))" "q \<tturnstile> \<phi> ([\<rho>,\<tau>] @ nenv)"
      using LeastI[of "\<lambda> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)" ?\<alpha>] by auto
    with \<open>q\<in>G\<close> \<open>\<rho>\<in>M\<close> \<open>nenv\<in>_\<close> \<open>arity(\<phi>)\<le> 2 #+ length(nenv)\<close>
    have "M[G], map(val(G),[\<rho>,\<tau>] @ nenv) \<Turnstile> \<phi>"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> generic, of "[\<rho>,\<tau>] @ nenv"] by auto
    moreover from \<open>x\<in>c\<close> \<open>c\<in>M[G]\<close>
    have "x\<in>M[G]" using transitivity_MG by simp
    moreover
    note \<open>M[G],[x,v] @ env\<Turnstile> \<phi>\<close> \<open>env = map(val(G),nenv)\<close> \<open>\<tau>\<in>M\<close> \<open>val(G,\<rho>)=x\<close>
      \<open>univalent(##M[G],_,_)\<close> \<open>x\<in>c\<close> \<open>v\<in>M[G]\<close>
    ultimately
    have "v=val(G,\<tau>)"
      using GenExtI[of \<tau> G] unfolding univalent_def by (auto)
    from \<open>\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))\<close> \<open>Ord(f(_))\<close>  \<open>f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "\<tau> \<in> Vset(?sup)"
      using Vset_Ord_rank_iff lt_Union_iff[of _ "rank(\<tau>)"] by auto
    with \<open>\<tau>\<in>M\<close>
    have "val(G,\<tau>) \<in> val(G,?big_name)"
      using domain_of_prod[of one "{one}" "{x\<in>Vset(?sup). x \<in> M}" ] def_val[of G ?big_name]
        one_in_G[OF generic] one_in_P  by (auto simp del: Vset_rank_iff)
    with \<open>v=val(G,\<tau>)\<close>
    have "v \<in> val(G,{x\<in>Vset(?sup). x \<in> M} \<times> {one})"
      by simp
  }
  then
  have "{v. x\<in>c, ?R(x,v)} \<subseteq> val(G,?big_name)" (is "?repl\<subseteq>?big")
    by blast
  with \<open>?big_name\<in>M\<close>
  have "?repl = {v\<in>?big. \<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env )}" (is "_ = ?rhs")
  proof(intro equalityI subsetI)
    fix v
    assume "v\<in>?repl"
    with \<open>?repl\<subseteq>?big\<close>
    obtain x where "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "v\<in>?big"
      using subsetD by auto
    with \<open>univalent(##M[G],_,_)\<close> \<open>c\<in>M[G]\<close>
    show "v \<in> ?rhs"
      unfolding univalent_def
      using transitivity_MG ReplaceI[of "\<lambda> x v. \<exists>x\<in>c. M[G], [x, v] @ env \<Turnstile> \<phi>"] by blast
  next
    fix v
    assume "v\<in>?rhs"
    then
    obtain x where
      "v\<in>val(G, ?big_name)" "M[G], [x, v] @ env \<Turnstile> \<phi>" "x\<in>c"
      by blast
    moreover from this \<open>c\<in>M[G]\<close>
    have "v\<in>M[G]" "x\<in>M[G]"
      using transitivity_MG GenExtI[OF \<open>?big_name\<in>_\<close>,of G] by auto
    moreover from calculation \<open>univalent(##M[G],_,_)\<close>
    have "?R(x,y) \<Longrightarrow> y = v" for y
      unfolding univalent_def by auto
    ultimately
    show "v\<in>?repl"
      using ReplaceI[of ?R x v c]
      by blast
  qed
  moreover
  let ?\<psi> = "Exists(And(Member(0,2#+length(env)),\<phi>))"
  have "v\<in>M[G] \<Longrightarrow> (\<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>) \<longleftrightarrow> M[G], [v] @ env @ [c] \<Turnstile> ?\<psi>"
    "arity(?\<psi>) \<le> 2 #+ length(env)" "?\<psi>\<in>formula"
    for v
  proof -
    fix v
    assume "v\<in>M[G]"
    with \<open>c\<in>M[G]\<close>
    have "nth(length(env)#+1,[v]@env@[c]) = c"
      using  \<open>env\<in>_\<close>nth_concat[of v c "M[G]" env]
      by auto
    note inMG= \<open>nth(length(env)#+1,[v]@env@[c]) = c\<close> \<open>c\<in>M[G]\<close> \<open>v\<in>M[G]\<close> \<open>env\<in>_\<close>
    show "(\<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>) \<longleftrightarrow> M[G], [v] @ env @ [c] \<Turnstile> ?\<psi>"
    proof
      assume "\<exists>x\<in>c. M[G], [x, v] @ env \<Turnstile> \<phi>"
      then obtain x where
        "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "x\<in>M[G]"
        using transitivity_MG[OF _ \<open>c\<in>M[G]\<close>]
        by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(\<phi>)\<le>2#+length(env)\<close> inMG
      show "M[G], [v] @ env @ [c] \<Turnstile> Exists(And(Member(0, 2 #+ length(env)), \<phi>))"
        using arity_sats_iff[of \<phi> "[c]" _ "[x,v]@env"]
        by auto
    next
      assume "M[G], [v] @ env @ [c] \<Turnstile> Exists(And(Member(0, 2 #+ length(env)), \<phi>))"
      with inMG
      obtain x where
        "x\<in>M[G]" "x\<in>c" "M[G], [x,v]@env@[c] \<Turnstile> \<phi>"
        by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(\<phi>)\<le>2#+length(env)\<close> inMG
      show "\<exists>x\<in>c. M[G], [x, v] @ env\<Turnstile> \<phi>"
        using arity_sats_iff[of \<phi> "[c]" _ "[x,v]@env"]
        by auto
    qed
  next
    from \<open>env\<in>_\<close> \<open>\<phi>\<in>_\<close>
    show "arity(?\<psi>)\<le>2#+length(env)"
      using pred_mono[OF _ \<open>arity(\<phi>)\<le>2#+length(env)\<close>] lt_trans[OF _ le_refl]
      by (auto simp add:nat_simp_union)
  next
    from \<open>\<phi>\<in>_\<close>
    show "?\<psi>\<in>formula" by simp
  qed
  moreover from this
  have "{v\<in>?big. \<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>} = {v\<in>?big. M[G], [v] @ env @ [c] \<Turnstile>  ?\<psi>}"
    using transitivity_MG[OF _ GenExtI, OF _ \<open>?big_name\<in>M\<close>]
    by simp
  moreover from calculation and \<open>env\<in>_\<close> \<open>c\<in>_\<close> \<open>?big\<in>M[G]\<close>
  have "{v\<in>?big. M[G] , [v] @ env @ [c] \<Turnstile> ?\<psi>} \<in> M[G]"
    using Collect_sats_in_MG by auto
  ultimately
  show ?thesis by simp
qed

theorem strong_replacement_in_MG:
  assumes
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 2 #+ length(env)" "env \<in> list(M[G])"
  shows
    "strong_replacement(##M[G],\<lambda>x v. sats(M[G],\<phi>,[x,v] @ env))"
proof -
  let ?R="\<lambda>x y . M[G], [x, y] @ env \<Turnstile> \<phi>"
  {
    fix A
    let ?Y="{v . x \<in> A, v\<in>M[G] \<and> ?R(x,v)}"
    assume 1: "(##M[G])(A)"
      "\<forall>x[##M[G]]. x \<in> A \<longrightarrow> (\<forall>y[##M[G]]. \<forall>z[##M[G]]. ?R(x,y) \<and> ?R(x,z) \<longrightarrow> y = z)"
    then
    have "univalent(##M[G], A, ?R)" "A\<in>M[G]"
      unfolding univalent_def by simp_all
    with assms \<open>A\<in>_\<close>
    have "(##M[G])(?Y)"
      using Replace_sats_in_MG by auto
    have "b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))" if "(##M[G])(b)" for b
    proof(rule)
      from \<open>A\<in>_\<close>
      show "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)" if "b \<in> ?Y"
        using that transitivity_MG by auto
    next
      show "b \<in> ?Y" if "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)"
      proof -
        from \<open>(##M[G])(b)\<close>
        have "b\<in>M[G]" by simp
        with that
        obtain x where "(##M[G])(x)" "x\<in>A" "b\<in>M[G] \<and> ?R(x,b)"
          by blast
        moreover from this 1 \<open>(##M[G])(b)\<close>
        have "x\<in>M[G]" "z\<in>M[G] \<and> ?R(x,z) \<Longrightarrow> b = z" for z
          by auto
        ultimately
        show ?thesis
          using ReplaceI[of "\<lambda> x y. y\<in>M[G] \<and> ?R(x,y)"] by auto
      qed
    qed
    then
    have "\<forall>b[##M[G]]. b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))"
      by simp
    with \<open>(##M[G])(?Y)\<close>
    have " (\<exists>Y[##M[G]]. \<forall>b[##M[G]]. b \<in> Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)))"
      by auto
  }
  then show ?thesis unfolding strong_replacement_def univalent_def
    by auto
qed

end (* context G_generic *)

end