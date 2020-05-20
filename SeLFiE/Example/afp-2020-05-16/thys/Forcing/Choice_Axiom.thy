section\<open>The Axiom of Choice in $M[G]$\<close>
theory Choice_Axiom
  imports Powerset_Axiom Pairing_Axiom Union_Axiom Extensionality_Axiom 
          Foundation_Axiom Powerset_Axiom Separation_Axiom 
          Replacement_Axiom Interface Infinity_Axiom
begin

definition 
  induced_surj :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "induced_surj(f,a,e) \<equiv> f-``(range(f)-a)\<times>{e} \<union> restrict(f,f-``a)"
  
lemma domain_induced_surj: "domain(induced_surj(f,a,e)) = domain(f)"
  unfolding induced_surj_def using domain_restrict domain_of_prod by auto
    
lemma range_restrict_vimage: 
  assumes "function(f)"
  shows "range(restrict(f,f-``a)) \<subseteq> a"
proof
  from assms 
  have "function(restrict(f,f-``a))" 
    using function_restrictI by simp
  fix y
  assume "y \<in> range(restrict(f,f-``a))"
  then 
  obtain x where "\<langle>x,y\<rangle> \<in> restrict(f,f-``a)"  "x \<in> f-``a" "x\<in>domain(f)"
    using domain_restrict domainI[of _ _ "restrict(f,f-``a)"] by auto
  moreover 
  note \<open>function(restrict(f,f-``a))\<close> 
  ultimately 
  have "y = restrict(f,f-``a)`x" 
    using function_apply_equality by blast
  also from \<open>x \<in> f-``a\<close> 
  have "restrict(f,f-``a)`x = f`x" 
    by simp
  finally 
  have "y=f`x" .
  moreover from assms \<open>x\<in>domain(f)\<close> 
  have "\<langle>x,f`x\<rangle> \<in> f" 
    using function_apply_Pair by auto 
  moreover 
  note assms \<open>x \<in> f-``a\<close> 
  ultimately 
  show "y\<in>a"
    using function_image_vimage[of f a] by auto
qed
  
lemma induced_surj_type: 
  assumes
    "function(f)" (* "relation(f)" (* a function can contain nonpairs *) *)
  shows 
    "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    and
    "x \<in> f-``a \<Longrightarrow> induced_surj(f,a,e)`x = f`x" 
proof -
  let ?f1="f-``(range(f)-a) \<times> {e}" and ?f2="restrict(f, f-``a)"
  have "domain(?f2) = domain(f) \<inter> f-``a"
    using domain_restrict by simp
  moreover from assms 
  have 1: "domain(?f1) = f-``(range(f))-f-``a"
    using domain_of_prod function_vimage_Diff by simp
  ultimately 
  have "domain(?f1) \<inter> domain(?f2) = 0"
    by auto
  moreover 
  have "function(?f1)" "relation(?f1)" "range(?f1) \<subseteq> {e}"
    unfolding function_def relation_def range_def by auto
  moreover from this and assms 
  have "?f1: domain(?f1) \<rightarrow> range(?f1)"
    using function_imp_Pi by simp
  moreover from assms 
  have "?f2: domain(?f2) \<rightarrow> range(?f2)"
    using function_imp_Pi[of "restrict(f, f -`` a)"] function_restrictI by simp
  moreover from assms 
  have "range(?f2) \<subseteq> a" 
    using range_restrict_vimage by simp
  ultimately 
  have "induced_surj(f,a,e): domain(?f1) \<union> domain(?f2) \<rightarrow> {e} \<union> a"
    unfolding induced_surj_def using fun_is_function fun_disjoint_Un fun_weaken_type by simp
  moreover 
  have "domain(?f1) \<union> domain(?f2) = domain(f)"
    using domain_restrict domain_of_prod by auto 
  ultimately
  show "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    by simp
  assume "x \<in> f-``a"
  then 
  have "?f2`x = f`x"
    using restrict by simp
  moreover from \<open>x \<in> f-``a\<close> and 1 
  have "x \<notin> domain(?f1)"
    by simp
  ultimately 
  show "induced_surj(f,a,e)`x = f`x" 
    unfolding induced_surj_def using fun_disjoint_apply2[of x ?f1 ?f2] by simp
qed
  
lemma induced_surj_is_surj : 
  assumes 
    "e\<in>a" "function(f)" "domain(f) = \<alpha>" "\<And>y. y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" 
  shows
    "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
  unfolding surj_def
proof (intro CollectI ballI)
  from assms 
  show "induced_surj(f,a,e): \<alpha> \<rightarrow> a"
    using induced_surj_type[of f a e] cons_eq cons_absorb by simp
  fix y
  assume "y \<in> a"
  with assms 
  have "\<exists>x\<in>\<alpha>. f ` x = y" 
    by simp
  then
  obtain x where "x\<in>\<alpha>" "f ` x = y" by auto
  with \<open>y\<in>a\<close> assms
  have "x\<in>f-``a" 
    using vimage_iff function_apply_Pair[of f x] by auto
  with \<open>f ` x = y\<close> assms
  have "induced_surj(f, a, e) ` x = y"
    using induced_surj_type by simp
  with \<open>x\<in>\<alpha>\<close> show
    "\<exists>x\<in>\<alpha>. induced_surj(f, a, e) ` x = y" by auto
qed
  
context G_generic 
begin

definition
  upair_name :: "i \<Rightarrow> i \<Rightarrow> i" where
  "upair_name(\<tau>,\<rho>) \<equiv> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}"

definition
  is_upair_name :: "[i,i,i] \<Rightarrow> o" where
  "is_upair_name(x,y,z) \<equiv> \<exists>xo\<in>M. \<exists>yo\<in>M. pair(##M,x,one,xo) \<and> pair(##M,y,one,yo) \<and> 
                                       upair(##M,xo,yo,z)"

lemma upair_name_abs : 
  assumes "x\<in>M" "y\<in>M" "z\<in>M" 
  shows "is_upair_name(x,y,z) \<longleftrightarrow> z = upair_name(x,y)" 
  unfolding is_upair_name_def upair_name_def using assms one_in_M pair_in_M_iff by simp

lemma upair_name_closed :
  "\<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> upair_name(x,y)\<in>M" 
  unfolding upair_name_def using upair_in_M_iff pair_in_M_iff one_in_M by simp

definition
  upair_name_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "upair_name_fm(x,y,o,z) \<equiv> Exists(Exists(And(pair_fm(x#+2,o#+2,1),
                                          And(pair_fm(y#+2,o#+2,0),upair_fm(1,0,z#+2)))))" 

lemma upair_name_fm_type[TC] :
    "\<lbrakk> s\<in>nat;x\<in>nat;y\<in>nat;o\<in>nat\<rbrakk> \<Longrightarrow> upair_name_fm(s,x,y,o)\<in>formula"
  unfolding upair_name_fm_def by simp

lemma sats_upair_name_fm :
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)""nth(o,env)=one" 
  shows 
    "sats(M,upair_name_fm(x,y,o,z),env) \<longleftrightarrow> is_upair_name(nth(x,env),nth(y,env),nth(z,env))"
  unfolding upair_name_fm_def is_upair_name_def using assms by simp

definition
  opair_name :: "i \<Rightarrow> i \<Rightarrow> i" where
  "opair_name(\<tau>,\<rho>) \<equiv> upair_name(upair_name(\<tau>,\<tau>),upair_name(\<tau>,\<rho>))"

definition
  is_opair_name :: "[i,i,i] \<Rightarrow> o" where
  "is_opair_name(x,y,z) \<equiv> \<exists>upxx\<in>M. \<exists>upxy\<in>M. is_upair_name(x,x,upxx) \<and> is_upair_name(x,y,upxy)
                                          \<and> is_upair_name(upxx,upxy,z)" 

lemma opair_name_abs : 
  assumes "x\<in>M" "y\<in>M" "z\<in>M" 
  shows "is_opair_name(x,y,z) \<longleftrightarrow> z = opair_name(x,y)" 
  unfolding is_opair_name_def opair_name_def using assms upair_name_abs upair_name_closed by simp

lemma opair_name_closed :
  "\<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> opair_name(x,y)\<in>M" 
  unfolding opair_name_def using upair_name_closed by simp

definition
  opair_name_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "opair_name_fm(x,y,o,z) \<equiv> Exists(Exists(And(upair_name_fm(x#+2,x#+2,o#+2,1),
                    And(upair_name_fm(x#+2,y#+2,o#+2,0),upair_name_fm(1,0,o#+2,z#+2)))))" 

lemma opair_name_fm_type[TC] :
    "\<lbrakk> s\<in>nat;x\<in>nat;y\<in>nat;o\<in>nat\<rbrakk> \<Longrightarrow> opair_name_fm(s,x,y,o)\<in>formula"
  unfolding opair_name_fm_def by simp

lemma sats_opair_name_fm :
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)""nth(o,env)=one" 
  shows 
    "sats(M,opair_name_fm(x,y,o,z),env) \<longleftrightarrow> is_opair_name(nth(x,env),nth(y,env),nth(z,env))"
  unfolding opair_name_fm_def is_opair_name_def using assms sats_upair_name_fm by simp

lemma val_upair_name : "val(G,upair_name(\<tau>,\<rho>)) = {val(G,\<tau>),val(G,\<rho>)}"
  unfolding upair_name_def using val_Upair  generic one_in_G one_in_P by simp
    
lemma val_opair_name : "val(G,opair_name(\<tau>,\<rho>)) = \<langle>val(G,\<tau>),val(G,\<rho>)\<rangle>"
  unfolding opair_name_def Pair_def using val_upair_name  by simp
    
lemma val_RepFun_one: "val(G,{\<langle>f(x),one\<rangle> . x\<in>a}) = {val(G,f(x)) . x\<in>a}"
proof -
  let ?A = "{f(x) . x \<in> a}"
  let ?Q = "\<lambda>\<langle>x,p\<rangle> . p = one"
  have "one \<in> P\<inter>G" using generic one_in_G one_in_P by simp
  have "{\<langle>f(x),one\<rangle> . x \<in> a} = {t \<in> ?A \<times> P . ?Q(t)}" 
    using one_in_P by force
  then
  have "val(G,{\<langle>f(x),one\<rangle>  . x \<in> a}) = val(G,{t \<in> ?A \<times> P . ?Q(t)})"
    by simp
  also
  have "... = {val(G,t) .. t \<in> ?A , \<exists>p\<in>P\<inter>G . ?Q(\<langle>t,p\<rangle>)}"
    using val_of_name_alt by simp
  also
  have "... = {val(G,t) . t \<in> ?A }"
    using \<open>one\<in>P\<inter>G\<close> by force
  also
  have "... = {val(G,f(x)) . x \<in> a}"
    by auto
  finally show ?thesis by simp
qed

subsection\<open>$M[G]$ is a transitive model of ZF\<close>

interpretation mgzf: M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG 
    extensionality_in_MG power_in_MG foundation_in_MG  
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

(* y = opair_name(check(\<beta>),s`\<beta>) *)
definition
  is_opname_check :: "[i,i,i] \<Rightarrow> o" where
  "is_opname_check(s,x,y) \<equiv> \<exists>chx\<in>M. \<exists>sx\<in>M. is_check(x,chx) \<and> fun_apply(##M,s,x,sx) \<and> 
                             is_opair_name(chx,sx,y)" 

definition
  opname_check_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "opname_check_fm(s,x,y,o) \<equiv> Exists(Exists(And(check_fm(2#+x,2#+o,1),
                              And(fun_apply_fm(2#+s,2#+x,0),opair_name_fm(1,0,2#+o,2#+y)))))"

lemma opname_check_fm_type[TC] :
  "\<lbrakk> s\<in>nat;x\<in>nat;y\<in>nat;o\<in>nat\<rbrakk> \<Longrightarrow> opname_check_fm(s,x,y,o)\<in>formula"
  unfolding opname_check_fm_def by simp

lemma sats_opname_check_fm:
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)" "nth(o,env)=one" 
          "y<length(env)"
  shows 
    "sats(M,opname_check_fm(x,y,z,o),env) \<longleftrightarrow> is_opname_check(nth(x,env),nth(y,env),nth(z,env))"
  unfolding opname_check_fm_def is_opname_check_def 
  using assms sats_check_fm sats_opair_name_fm one_in_M by simp


lemma opname_check_abs :
  assumes "s\<in>M" "x\<in>M" "y\<in>M" 
  shows "is_opname_check(s,x,y) \<longleftrightarrow> y = opair_name(check(x),s`x)" 
  unfolding is_opname_check_def  
  using assms check_abs check_in_M opair_name_abs apply_abs apply_closed by simp

lemma repl_opname_check :
  assumes
    "A\<in>M" "f\<in>M" 
  shows
   "{opair_name(check(x),f`x). x\<in>A}\<in>M"
proof -
  have "arity(opname_check_fm(3,0,1,2))= 4" 
    unfolding opname_check_fm_def opair_name_fm_def upair_name_fm_def
          check_fm_def rcheck_fm_def trans_closure_fm_def is_eclose_fm_def mem_eclose_fm_def
         is_Hcheck_fm_def Replace_fm_def PHcheck_fm_def finite_ordinal_fm_def is_iterates_fm_def
             is_wfrec_fm_def is_recfun_fm_def restriction_fm_def pre_image_fm_def eclose_n_fm_def
        is_nat_case_fm_def quasinat_fm_def Memrel_fm_def singleton_fm_def fm_defs iterates_MH_fm_def
    by (simp add:nat_simp_union)
  moreover
  have "x\<in>A \<Longrightarrow> opair_name(check(x), f ` x)\<in>M" for x
    using assms opair_name_closed apply_closed transitivity check_in_M
    by simp
  ultimately
  show ?thesis using assms opname_check_abs[of f] sats_opname_check_fm
        one_in_M
        Repl_in_M[of "opname_check_fm(3,0,1,2)" "[one,f]" "is_opname_check(f)" 
                    "\<lambda>x. opair_name(check(x),f`x)"] 
    by simp
qed



theorem choice_in_MG: 
  assumes "choice_ax(##M)"
  shows "choice_ax(##M[G])"
proof -
  {
    fix a
    assume "a\<in>M[G]"
    then
    obtain \<tau> where "\<tau>\<in>M" "val(G,\<tau>) = a" 
      using GenExt_def by auto
    with \<open>\<tau>\<in>M\<close>
    have "domain(\<tau>)\<in>M"
      using domain_closed by simp
    then
    obtain s \<alpha> where "s\<in>surj(\<alpha>,domain(\<tau>))" "Ord(\<alpha>)" "s\<in>M" "\<alpha>\<in>M"
      using assms choice_ax_abs by auto
    then
    have "\<alpha>\<in>M[G]"         
      using M_subset_MG generic one_in_G subsetD by blast
    let ?A="domain(\<tau>)\<times>P"
    let ?g = "{opair_name(check(\<beta>),s`\<beta>). \<beta>\<in>\<alpha>}"
    have "?g \<in> M" using \<open>s\<in>M\<close> \<open>\<alpha>\<in>M\<close> repl_opname_check by simp
    let ?f_dot="{\<langle>opair_name(check(\<beta>),s`\<beta>),one\<rangle>. \<beta>\<in>\<alpha>}"
    have "?f_dot = ?g \<times> {one}" by blast
    from one_in_M have "{one} \<in> M" using singletonM by simp
    define f where
      "f \<equiv> val(G,?f_dot)" 
    from \<open>{one}\<in>M\<close> \<open>?g\<in>M\<close> \<open>?f_dot = ?g\<times>{one}\<close> 
    have "?f_dot\<in>M" 
      using cartprod_closed by simp
    then
    have "f \<in> M[G]"
      unfolding f_def by (blast intro:GenExtI)
    have "f = {val(G,opair_name(check(\<beta>),s`\<beta>)) . \<beta>\<in>\<alpha>}"
      unfolding f_def using val_RepFun_one by simp
    also
    have "... = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}"
      using val_opair_name valcheck generic one_in_G one_in_P by simp
    finally
    have "f = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}" .
    then
    have 1: "domain(f) = \<alpha>" "function(f)"
      unfolding function_def by auto
    have 2: "y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" for y
    proof -
      fix y
      assume
        "y \<in> a"
      with \<open>val(G,\<tau>) = a\<close> 
      obtain \<sigma> where  "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) = y"
        using elem_of_val[of y _ \<tau>] by blast
      with \<open>s\<in>surj(\<alpha>,domain(\<tau>))\<close> 
      obtain \<beta> where "\<beta>\<in>\<alpha>" "s`\<beta> = \<sigma>" 
        unfolding surj_def by auto
      with \<open>val(G,\<sigma>) = y\<close>
      have "val(G,s`\<beta>) = y" 
        by simp
      with \<open>f = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}\<close> \<open>\<beta>\<in>\<alpha>\<close>
      have "\<langle>\<beta>,y\<rangle>\<in>f" 
        by auto
      with \<open>function(f)\<close>
      have "f`\<beta> = y"
        using function_apply_equality by simp
      with \<open>\<beta>\<in>\<alpha>\<close> show
        "\<exists>\<beta>\<in>\<alpha>. f ` \<beta> = y" 
        by auto
    qed
    then
    have "\<exists>\<alpha>\<in>(M[G]). \<exists>f'\<in>(M[G]). Ord(\<alpha>) \<and> f' \<in> surj(\<alpha>,a)"
    proof (cases "a=0")
      case True
      then
      have "0\<in>surj(0,a)" 
        unfolding surj_def by simp
      then
      show ?thesis using zero_in_MG by auto
    next
      case False
      with \<open>a\<in>M[G]\<close> 
      obtain e where "e\<in>a" "e\<in>M[G]" 
        using transitivity_MG by blast
      with 1 and 2
      have "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
        using induced_surj_is_surj by simp
      moreover from \<open>f\<in>M[G]\<close> \<open>a\<in>M[G]\<close> \<open>e\<in>M[G]\<close>
      have "induced_surj(f,a,e) \<in> M[G]"
        unfolding induced_surj_def 
        by (simp flip: setclass_iff)
      moreover note
        \<open>\<alpha>\<in>M[G]\<close> \<open>Ord(\<alpha>)\<close>
      ultimately show ?thesis by auto
    qed
  }
  then
  show ?thesis using mgzf.choice_ax_abs by simp
qed
  
end (* G_generic_extra_repl *)
  
end