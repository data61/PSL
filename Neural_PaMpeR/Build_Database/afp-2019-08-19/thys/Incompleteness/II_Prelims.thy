chapter\<open>Syntactic Preliminaries for the Second Incompleteness Theorem\<close>

theory II_Prelims
imports Pf_Predicates
begin

declare IndP.simps [simp del]

lemma VarP_Var [intro]: "H \<turnstile> VarP \<lceil>Var i\<rceil>"
proof -
  have "{} \<turnstile> VarP \<lceil>Var i\<rceil>"
    by (auto simp: Sigma_fm_imp_thm [OF VarP_sf] ground_fm_aux_def supp_conv_fresh)
  thus ?thesis
    by (rule thin0)
qed

lemma VarP_neq_IndP: "{t EQ v, VarP v, IndP t} \<turnstile> Fls"
proof -
  obtain m::name where "atom m \<sharp> (t,v)"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (auto simp: VarP_def IndP.simps [of m])
    apply (rule cut_same [of _ "OrdP (Q_Ind (Var m))"])
    apply (blast intro: Sym Trans OrdP_cong [THEN Iff_MP_same])
    by (metis OrdP_HPairE)
qed

lemma OrdP_ORD_OF [intro]: "H \<turnstile> OrdP (ORD_OF n)"
proof -
  have "{} \<turnstile> OrdP (ORD_OF n)"
    by (induct n) (auto simp: OrdP_SUCC_I)
  thus ?thesis
    by (rule thin0)
qed
 
lemma Mem_HFun_Sigma_OrdP: "{HPair t u IN f, HFun_Sigma f} \<turnstile> OrdP t"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name
    where "atom z \<sharp> (f,t,u,z',x,y,x',y')"  "atom z' \<sharp> (f,t,u,x,y,x',y')"
       "atom x \<sharp> (f,t,u,y,x',y')"  "atom y \<sharp> (f,t,u,x',y')" 
       "atom x' \<sharp> (f,t,u,y')"  "atom y' \<sharp> (f,t,u)"
    by (metis obtain_fresh) 
  thus ?thesis 
  apply (simp add: HFun_Sigma.simps [of z f z' x y x' y'])
  apply (rule All2_E [where x="HPair t u", THEN rotate2], auto)
  apply (rule All2_E [where x="HPair t u"], auto intro: OrdP_cong [THEN Iff_MP2_same])
  done
qed

section \<open>NotInDom\<close>

nominal_function NotInDom :: "tm \<Rightarrow> tm \<Rightarrow> fm" 
  where "atom z \<sharp> (t, r) \<Longrightarrow> NotInDom t r = All z (Neg (HPair t (Var z) IN r))"
by (auto simp: eqvt_def NotInDom_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma NotInDom_fresh_iff [simp]: "a \<sharp> NotInDom t r \<longleftrightarrow> a \<sharp> (t, r)"
proof -
  obtain j::name where "atom j \<sharp> (t,r)"
    by (rule obtain_fresh)
  thus ?thesis
    by auto
qed

lemma subst_fm_NotInDom [simp]: "(NotInDom t r)(i::=x) = NotInDom (subst i x t) (subst i x r)"
proof -
  obtain j::name where "atom j \<sharp> (i,x,t,r)"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp: NotInDom.simps [of j])
qed

lemma NotInDom_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> r EQ r' \<Longrightarrow> H \<turnstile> NotInDom t r IFF NotInDom t' r'"
  by (rule P2_cong) auto

lemma NotInDom_Zero: "H \<turnstile> NotInDom t Zero"
proof -
  obtain z::name where "atom z \<sharp> t"
    by (metis obtain_fresh) 
  hence "{} \<turnstile> NotInDom t Zero"
    by (auto simp: fresh_Pair)
  thus ?thesis
    by (rule thin0)
qed

lemma NotInDom_Fls: "{HPair d d' IN r, NotInDom d r} \<turnstile> A"
proof -
  obtain z::name where "atom z \<sharp> (d,r)"
    by (metis obtain_fresh) 
  hence "{HPair d d' IN r, NotInDom d r} \<turnstile> Fls"
    by (auto intro!: Ex_I [where x=d'])
  thus ?thesis 
    by (metis ExFalso)
qed

lemma NotInDom_Contra: "H \<turnstile> NotInDom d r \<Longrightarrow> H \<turnstile> HPair x y IN r \<Longrightarrow> insert (x EQ d) H \<turnstile> A"
by (rule NotInDom_Fls [THEN cut2, THEN ExFalso])
   (auto intro: thin1 NotInDom_cong [OF Assume Refl, THEN Iff_MP2_same])


section \<open>Restriction of a Sequence to a Domain\<close>

nominal_function RestrictedP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom x \<sharp> (y,f,k,g); atom y \<sharp> (f,k,g)\<rbrakk> \<Longrightarrow>
    RestrictedP f k g =
      g SUBS f AND
      All x (All y (HPair (Var x) (Var y) IN g IFF 
                    (Var x) IN k AND HPair (Var x) (Var y) IN f))"
by (auto simp: eqvt_def RestrictedP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma RestrictedP_fresh_iff [simp]: "a \<sharp> RestrictedP f k g \<longleftrightarrow> a \<sharp> f \<and> a \<sharp> k \<and> a \<sharp> g"       
proof -
  obtain x::name and y::name where "atom x \<sharp> (y,f,k,g)" "atom y \<sharp> (f,k,g)"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma subst_fm_RestrictedP [simp]:
  "(RestrictedP f k g)(i::=u) = RestrictedP (subst i u f) (subst i u k) (subst i u g)"
proof -
  obtain x::name and y::name  where "atom x \<sharp> (y,f,k,g,i,u)" "atom y \<sharp> (f,k,g,i,u)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: RestrictedP.simps [of x y])
qed

lemma RestrictedP_cong: 
  "\<lbrakk>H \<turnstile> f EQ f'; H \<turnstile> k EQ A'; H \<turnstile> g EQ g'\<rbrakk> 
   \<Longrightarrow> H \<turnstile> RestrictedP f k g IFF RestrictedP f' A' g'"
  by (rule P3_cong) auto

lemma RestrictedP_Zero: "H \<turnstile> RestrictedP Zero k Zero"
proof -
  obtain x::name and y::name  where "atom x \<sharp> (y,k)" "atom y \<sharp> (k)"
    by (metis obtain_fresh)
  hence "{} \<turnstile> RestrictedP Zero k Zero"
    by (auto simp: RestrictedP.simps [of x y])
  thus ?thesis
    by (rule thin0)
qed

lemma RestrictedP_Mem: "{ RestrictedP s k s', HPair a b IN s, a IN k } \<turnstile> HPair a b IN s'"
proof -
  obtain x::name and y::name where "atom x \<sharp> (y,s,k,s',a,b)" "atom y \<sharp> (s,k,s',a,b)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: RestrictedP.simps [of x y])
    apply (rule All_E [where x=a, THEN rotate2], auto)
    apply (rule All_E [where x=b], auto intro: Iff_E2)
    done
qed

lemma RestrictedP_imp_Subset: "{RestrictedP s k s'} \<turnstile> s' SUBS s"
proof -
  obtain x::name and y::name where "atom x \<sharp> (y,s,k,s')" "atom y \<sharp> (s,k,s')"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: RestrictedP.simps [of x y])
qed

lemma RestrictedP_Mem2: 
  "{ RestrictedP s k s', HPair a b IN s' } \<turnstile> HPair a b IN s AND a IN k"
proof -
  obtain x::name and y::name where "atom x \<sharp> (y,s,k,s',a,b)" "atom y \<sharp> (s,k,s',a,b)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: RestrictedP.simps [of x y] intro: Subset_D)
    apply (rule All_E [where x=a, THEN rotate2], auto)
    apply (rule All_E [where x=b], auto intro: Iff_E1)
    done
qed

lemma RestrictedP_Mem_D: "H \<turnstile> RestrictedP s k t \<Longrightarrow> H \<turnstile> a IN t \<Longrightarrow> insert (a IN s) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis RestrictedP_imp_Subset Subset_E cut1)

lemma RestrictedP_Eats:
  "{ RestrictedP s k s', a IN k } \<turnstile> RestrictedP (Eats s (HPair a b)) k (Eats s' (HPair a b))" (*<*)
proof -
  obtain x::name and y::name 
  where "atom x \<sharp> (y,s,k,s',a,b)" "atom y \<sharp> (s,k,s',a,b)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: RestrictedP.simps [of x y])
      apply (metis Assume Subset_Eats_I Subset_trans)
     apply (metis Mem_Eats_I2 Refl)
    apply (rule Swap, auto)
         apply (rule All_E [where x="Var x", THEN rotate2], auto)
         apply (rule All_E [where x="Var y"], simp)
         apply (metis Assume Conj_E Iff_E1)
        apply (blast intro: Subset_D)
       apply (blast intro: Mem_cong [THEN Iff_MP2_same])
      apply (metis Assume AssumeH(2) HPair_cong Mem_Eats_I2)
     apply (rule All_E [where x="Var x", THEN rotate3], auto)
     apply (rule All_E [where x="Var y"], simp)
     apply (metis Assume AssumeH(2) Conj_I Iff_E2 Mem_Eats_I1)
    apply (blast intro: Mem_Eats_I2 HPair_cong)
   done
qed (*>*)

lemma exists_RestrictedP: 
  assumes s: "atom s \<sharp> (f,k)"
  shows  "H \<turnstile> Ex s (RestrictedP f k (Var s))" (*<*)
proof -
  obtain j::name and x::name and y::name and z::name
    where atoms: "atom j \<sharp> (k,z,s)"  "atom x \<sharp> (j,k,z,s)"  "atom y \<sharp> (x,j,k,z,s)"  "atom z \<sharp> (s,k)"
    by (metis obtain_fresh) 
  have "{} \<turnstile> Ex s (RestrictedP (Var z) k (Var s))"
    apply (rule Ind [of j z]) using atoms s
    apply simp_all
    apply (rule Ex_I [where x=Zero], simp add: RestrictedP_Zero)
    apply (rule All_I)+
    apply (auto del: Ex_EH)
    apply (rule thin1)
    apply (rule Ex_E)
    proof (rule Cases [where A="Ex x (Ex y ((Var x) IN k AND Var j EQ HPair (Var x) (Var y)))"], auto)
      show "{Var x IN k, Var j EQ HPair (Var x) (Var y), RestrictedP (Var z) k (Var s)} 
            \<turnstile> Ex s (RestrictedP (Eats (Var z) (Var j)) k (Var s))"
        apply (rule Ex_I [where x="Eats (Var s) (HPair (Var x) (Var y))"])
        using atoms s apply auto
        apply (rule RestrictedP_cong [OF _ Refl Refl, THEN Iff_MP2_same])
        apply (blast intro: Eats_cong [OF Refl])
        apply (rule Var_Eq_subst_Iff [THEN rotate2, THEN Iff_MP_same])
        apply (auto intro: RestrictedP_Eats [THEN cut2])
        done
    next
      obtain u::name and v::name 
      where uv: "atom u \<sharp> (x,y,z,s,j,k)" "atom v \<sharp> (u,x,y,z,s,j,k)"
        by (metis obtain_fresh)
      show "{Neg (Ex x (Ex y (Var x IN k AND Var j EQ HPair (Var x) (Var y)))),
             RestrictedP (Var z) k (Var s)} \<turnstile>
             Ex s (RestrictedP (Eats (Var z) (Var j)) k (Var s))"
        apply (rule Ex_I [where x="Var s"]) 
        using uv atoms
        apply (auto simp: RestrictedP.simps [of u v])
         apply (metis Assume Subset_Eats_I Subset_trans)
        apply (rule Swap, auto)
           apply (rule All_E [THEN rotate4, of _ _ "Var u"], auto)
           apply (rule All_E [where x="Var v"], simp)
           apply (metis Assume Conj_E Iff_E1)
          apply (rule Mem_Eats_I1)
          apply (metis Assume AssumeH(3) Subset_D)
         apply (rule All_E [where x="Var u", THEN rotate5], auto)
         apply (rule All_E [where x="Var v"], simp)
         apply (metis Assume AssumeH(2) Conj_I Iff_E2)
        apply (rule ContraProve [THEN rotate3])
       apply (rule Ex_I [where x="Var u"], simp)
       apply (rule Ex_I [where x="Var v"], auto intro: Sym)
       done
    qed
  hence "{} \<turnstile> (Ex s (RestrictedP (Var z) k (Var s)))(z::=f)"
    by (rule Subst) simp
  thus ?thesis using atoms s
    by simp (rule thin0)
qed (*>*)    

lemma cut_RestrictedP: 
  assumes s: "atom s \<sharp> (f,k,A)" and "\<forall>C \<in> H. atom s \<sharp> C"
  shows  "insert (RestrictedP f k (Var s)) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  apply (rule cut_same [OF exists_RestrictedP [of s]])
  using assms apply auto
  done

lemma RestrictedP_NotInDom: "{ RestrictedP s k s', Neg (j IN k) } \<turnstile> NotInDom j s'"
proof -
  obtain x::name and y::name and z::name 
  where "atom x \<sharp> (y,s,j,k,s')" "atom y \<sharp> (s,j,k,s')" "atom z \<sharp> (s,j,k,s')"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: RestrictedP.simps [of x y] NotInDom.simps [of z])
    apply (rule All_E [where x=j, THEN rotate3], auto)
    apply (rule All_E, auto intro: Conj_E1 Iff_E1)
    done
qed

declare RestrictedP.simps [simp del]

section \<open>Applications to LstSeqP\<close>

lemma HFun_Sigma_Eats: 
  assumes "H \<turnstile> HFun_Sigma r" "H \<turnstile> NotInDom d r" "H \<turnstile> OrdP d"
    shows "H \<turnstile> HFun_Sigma (Eats r (HPair d d'))" (*<*)
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name and z''::name
    where "atom z'' \<sharp> (r,d,d',z,z',x,y,x',y')" 
      and "atom z \<sharp> (r,d,d',z',x,y,x',y')" and "atom z' \<sharp> (r,d,d',x,y,x',y')"
      and "atom x \<sharp> (r,d,d',y,x',y')" and "atom y \<sharp> (r,d,d',x',y')" 
      and "atom x' \<sharp> (r,d,d',y')" and "atom y' \<sharp> (r,d,d')"
    by (metis obtain_fresh) 
  hence "{ HFun_Sigma r, NotInDom d r, OrdP d } \<turnstile> HFun_Sigma (Eats r (HPair d d'))"
    apply (auto simp: HFun_Sigma.simps [of z _ z' x y x' y'])
      \<comment> \<open>case 1\<close>
       apply (rule Ex_I [where x = "Var z"], simp)
       apply (rule Neg_Imp_I, blast)
      apply (rule All_E [where x = "Var z'"], auto)
      \<comment> \<open>case 2\<close>
      apply (rule Ex_I [where x = "Var z"], simp)
      apply (rule Neg_Imp_I, blast)
      apply (rule All_E [where x = "Var z"], simp)
      apply (rule Imp_E, auto del: Disj_EH)
      apply (rule thin1)
      apply (rule thin1)
      apply (rule Ex_I [where x = "Var x"], simp)
      apply (rule Ex_I [where x = "Var y"], simp)
      apply (rule Ex_I [where x = d], simp)
      apply (rule Ex_I [where x = d'], auto)
      apply (blast intro: Disj_I1 OrdNotEqP_I NotInDom_Contra Mem_cong [THEN Iff_MP_same])
    \<comment> \<open>case 3\<close>
    apply (rule Ex_I [where x = "Var z'"])
    apply (subst subst_fm_Ex_with_renaming [where i'=z''] | subst subst_fm.simps)+
    apply (auto simp add: flip_fresh_fresh)
    apply (rule Ex_I [where x = "Var z'", THEN Swap], simp)
    apply (rule Neg_I)
    apply (rule Imp_E, auto del: Disj_EH)
    apply (rule thin1)
    apply (rule thin1)
    apply (rule Ex_I [where x = d], simp)
    apply (rule Ex_I [where x = d'], simp)
    apply (rule Ex_I [where x = "Var x"], simp)
    apply (rule Ex_I [where x = "Var y"], auto)
    apply (blast intro: Disj_I1 Sym_L OrdNotEqP_I NotInDom_Contra Mem_cong [THEN Iff_MP_same])
    \<comment> \<open>case 4\<close>
    apply (rule rotate2 [OF Swap])
    apply (rule Ex_I [where x = d], auto)
    apply (rule Ex_I [where x = d'], auto)
    apply (rule Ex_I [where x = d], auto)
    apply (rule Ex_I [where x = d'], auto intro: Disj_I2)
    done
  thus ?thesis using assms
    by (rule cut3)
qed (*>*)

lemma HFun_Sigma_single [iff]: "H \<turnstile> OrdP d \<Longrightarrow> H \<turnstile> HFun_Sigma (Eats Zero (HPair d d'))"
  by (metis HFun_Sigma_Eats HFun_Sigma_Zero NotInDom_Zero)

lemma LstSeqP_single [iff]: "H \<turnstile> LstSeqP (Eats Zero (HPair Zero x)) Zero x"
  by (auto simp: LstSeqP.simps intro!: OrdP_SUCC_I HDomain_Incl_Eats_I Mem_Eats_I2)

lemma NotInDom_LstSeqP_Eats: 
  "{ NotInDom (SUCC k) s, LstSeqP s k y } \<turnstile> LstSeqP (Eats s (HPair (SUCC k) z)) (SUCC k) z"
by (auto simp: LstSeqP.simps intro: HDomain_Incl_Eats_I Mem_Eats_I2 OrdP_SUCC_I HFun_Sigma_Eats)

lemma RestrictedP_HDomain_Incl: "{HDomain_Incl s k, RestrictedP s k s'} \<turnstile> HDomain_Incl s' k"
proof -
  obtain u::name and v::name and x::name and y::name and z::name 
    where "atom u \<sharp> (v,s,k,s')" "atom v \<sharp> (s,k,s')" 
          "atom x \<sharp> (s,k,s',u,v,y,z)" "atom y \<sharp> (s,k,s',u,v,z)" "atom z \<sharp> (s,k,s',u,v)"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (auto simp: HDomain_Incl.simps [of x _ _ y z])
    apply (rule Ex_I [where x="Var x"], auto)
    apply (rule Ex_I [where x="Var y"], auto)
    apply (rule Ex_I [where x="Var z"], simp)
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate2])
    apply (auto simp: RestrictedP.simps [of u v])
    apply (rule All_E [where x="Var x", THEN rotate2], auto)
    apply (rule All_E [where x="Var y"])
    apply (auto intro: Iff_E ContraProve Mem_cong [THEN Iff_MP_same])
    done
qed

lemma RestrictedP_HFun_Sigma: "{HFun_Sigma s, RestrictedP s k s'} \<turnstile> HFun_Sigma s'"
  by (metis Assume RestrictedP_imp_Subset Subset_HFun_Sigma rcut2)

lemma RestrictedP_LstSeqP: 
  "{ RestrictedP s (SUCC k) s', LstSeqP s k y } \<turnstile> LstSeqP s' k y"
  by (auto simp: LstSeqP.simps 
           intro: Mem_Neg_refl cut2 [OF RestrictedP_HDomain_Incl]  
                               cut2 [OF RestrictedP_HFun_Sigma] cut3 [OF RestrictedP_Mem])

lemma RestrictedP_LstSeqP_Eats: 
  "{ RestrictedP s (SUCC k) s', LstSeqP s k y }
   \<turnstile> LstSeqP (Eats s' (HPair (SUCC k) z)) (SUCC k) z"
by (blast intro: Mem_Neg_refl cut2 [OF NotInDom_LstSeqP_Eats] 
                              cut2 [OF RestrictedP_NotInDom] cut2 [OF RestrictedP_LstSeqP])


section\<open>Ordinal Addition\<close>

subsection\<open>Predicate form, defined on sequences\<close>

nominal_function SeqHaddP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (sl,s,k,j); atom sl \<sharp> (s,j)\<rbrakk> \<Longrightarrow>
    SeqHaddP s j k y = LstSeqP s k y AND
          HPair Zero j IN s AND
          All2 l k (Ex sl (HPair (Var l) (Var sl) IN s AND
                           HPair (SUCC (Var l)) (SUCC (Var sl)) IN s))"
by (auto simp: eqvt_def SeqHaddP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma SeqHaddP_fresh_iff [simp]: "a \<sharp> SeqHaddP s j k y \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> j \<and> a \<sharp> k \<and> a \<sharp> y"
proof -
  obtain l::name and sl::name where "atom l \<sharp> (sl,s,k,j)" "atom sl \<sharp> (s,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by force
qed

lemma SeqHaddP_subst [simp]:
  "(SeqHaddP s j k y)(i::=t) = SeqHaddP (subst i t s) (subst i t j) (subst i t k) (subst i t y)"
proof -
  obtain l::name and sl::name where "atom l \<sharp> (s,k,j,sl,t,i)" "atom sl \<sharp> (s,k,j,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHaddP.simps [where l=l and sl=sl])
qed

declare SeqHaddP.simps [simp del]

nominal_function HaddP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (x,y,z)\<rbrakk> \<Longrightarrow>
    HaddP x y z = Ex s (SeqHaddP (Var s) x y z)"
by (auto simp: eqvt_def HaddP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma HaddP_fresh_iff [simp]: "a \<sharp> HaddP x y z \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y \<and> a \<sharp> z" 
proof -
  obtain s::name where "atom s \<sharp> (x,y,z)"
    by (metis obtain_fresh)
  thus ?thesis
    by force
qed

lemma HaddP_subst [simp]: "(HaddP x y z)(i::=t) = HaddP (subst i t x) (subst i t y) (subst i t z)"
proof -
  obtain s::name where "atom s \<sharp> (x,y,z,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: HaddP.simps [of s])
qed

lemma HaddP_cong: "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'; H \<turnstile> v EQ v'\<rbrakk> \<Longrightarrow> H \<turnstile> HaddP t u v IFF HaddP t' u' v'"
  by (rule P3_cong) auto

declare HaddP.simps [simp del]

lemma HaddP_Zero2: "H \<turnstile> HaddP x Zero x"
proof -
  obtain s::name and l::name and sl::name where "atom l \<sharp> (sl,s,x)" "atom sl \<sharp> (s,x)" "atom s \<sharp> x"
    by (metis obtain_fresh)
  hence "{} \<turnstile> HaddP x Zero x"
    by (auto simp: HaddP.simps [of s] SeqHaddP.simps [of l sl]
          intro!: Mem_Eats_I2 Ex_I [where x="Eats Zero (HPair Zero x)"])
  thus ?thesis
    by (rule thin0)
qed

lemma HaddP_imp_OrdP: "{HaddP x y z} \<turnstile> OrdP y" 
proof -
  obtain s::name and l::name and sl::name
    where "atom l \<sharp> (sl,s,x,y,z)" "atom sl \<sharp> (s,x,y,z)" "atom s \<sharp> (x,y,z)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: HaddP.simps [of s] SeqHaddP.simps [of l sl] LstSeqP.simps)
qed

lemma HaddP_SUCC2: "{HaddP x y z} \<turnstile> HaddP x (SUCC y) (SUCC z)" (*<*)
proof -
  obtain s::name and s'::name and l::name and sl::name
    where "atom s' \<sharp> (l,sl,s,x,y,z)" "atom l \<sharp> (sl,s,x,y,z)" "atom sl \<sharp> (s,x,y,z)" "atom s \<sharp> (x,y,z)"
    by (metis obtain_fresh)
  hence "{HaddP x y z, OrdP y} \<turnstile> HaddP x (SUCC y) (SUCC z)"
    apply (auto simp: HaddP.simps [of s] SeqHaddP.simps [of l sl])
    apply (rule cut_RestrictedP [of s' "Var s" "SUCC y"], auto)
    apply (rule Ex_I [where x="Eats (Var s') (HPair (SUCC y) (SUCC z))"])
       apply (auto intro!: Mem_SUCC_EH)
       apply (metis rotate2 RestrictedP_LstSeqP_Eats rotate3 thin1)
      apply (blast intro: Mem_Eats_I1 cut3 [OF RestrictedP_Mem] cut1 [OF Zero_In_SUCC])
     apply (rule Ex_I [where x="Var l"], auto)
     apply (rule Ex_I [where x="Var sl"], auto)
     apply (blast intro: Mem_Eats_I1 cut3 [OF RestrictedP_Mem] Mem_SUCC_I1)
    apply (blast intro: Mem_Eats_I1 cut3 [OF RestrictedP_Mem] OrdP_IN_SUCC)
   apply (rule ContraProve [THEN rotate2])
   apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], simp add: LstSeqP.simps)
   apply (rule Ex_I [where x=z])
   apply (force intro: Mem_Eats_I1 Mem_Eats_I2 cut3 [OF RestrictedP_Mem] Mem_SUCC_I2)
   done
 thus ?thesis
   by (metis Assume HaddP_imp_OrdP cut2)
qed (*>*)

subsection\<open>Proving that these relations are functions\<close>

lemma SeqHaddP_Zero_E: "{SeqHaddP s w Zero z} \<turnstile> w EQ z"
proof -
  obtain l::name and sl::name where "atom l \<sharp> (s,w,z,sl)" "atom sl \<sharp> (s,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHaddP.simps [of l sl] LstSeqP.simps intro: HFun_Sigma_E)
qed

lemma SeqHaddP_SUCC_lemma:
  assumes y': "atom y' \<sharp> (s,j,k,y)"
  shows "{SeqHaddP s j (SUCC k) y} \<turnstile> Ex y' (SeqHaddP s j k (Var y') AND y EQ SUCC (Var y'))"
proof -
  obtain l::name and sl::name  where "atom l \<sharp> (s,j,k,y,y',sl)" "atom sl \<sharp> (s,j,k,y,y')"
    by (metis obtain_fresh)
  thus ?thesis using y'
    apply (auto simp: SeqHaddP.simps [where s=s and l=l and sl=sl])
    apply (rule All2_SUCC_E' [where t=k, THEN rotate2], auto)
    apply (auto intro!: Ex_I [where x="Var sl"])
    apply (blast intro: LstSeqP_SUCC) \<comment> \<open>showing @{term"SeqHaddP s j k (Var sl)"}\<close>
    apply (blast intro: LstSeqP_EQ)
    done
qed

lemma SeqHaddP_SUCC:
  assumes "H \<turnstile> SeqHaddP s j (SUCC k) y"  "atom y' \<sharp> (s,j,k,y)"
  shows "H \<turnstile> Ex y' (SeqHaddP s j k (Var y') AND y EQ SUCC (Var y'))"
  by (metis SeqHaddP_SUCC_lemma [THEN cut1] assms)

lemma SeqHaddP_unique: "{OrdP x, SeqHaddP s w x y, SeqHaddP s' w x y'} \<turnstile> y' EQ y" (*<*)
proof -
  obtain i::name and j::name and j'::name and k::name and sl::name and sl'::name 
     and l::name and ji::name and ji'::name
   where ij: "atom i \<sharp> (s,s',w,y,y')" "atom j \<sharp> (s,s',w,i,x,y,y')" "atom j' \<sharp> (s,s',w,i,j,x,y,y')"
     and atoms: "atom k \<sharp> (s,s',w,i,j,j')" "atom sl \<sharp> (s,s',w,i,j,j',k)" "atom sl' \<sharp> (s,s',w,i,j,j',k,sl)"
                "atom ji \<sharp> (s,s',w,i,j,j',k,sl,sl')"  "atom ji' \<sharp> (s,s',w,i,j,j',k,sl,sl',ji)"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} 
        \<turnstile> All j (All j' (SeqHaddP s w (Var i) (Var j) IMP (SeqHaddP s' w (Var i) (Var j') IMP Var j' EQ Var j)))"
    apply (rule OrdInd2H)
    using ij atoms apply auto 
    apply (metis SeqHaddP_Zero_E [THEN cut1] Assume AssumeH(2) Sym Trans)
    \<comment> \<open>SUCC case\<close>
    apply (rule cut_same [OF SeqHaddP_SUCC [where y' = ji and s=s]], auto)
    apply (rule cut_same [OF SeqHaddP_SUCC [where y' = ji' and s=s']], auto)
    apply (rule Ex_I [where x = "Var ji"], auto)
    apply (rule All_E [where x = "Var ji'"], auto)
    apply (blast intro: Trans [OF Hyp] Sym intro!: SUCC_cong)
    done
  hence "{OrdP (Var i)} 
         \<turnstile> (All j' (SeqHaddP s w (Var i) (Var j) IMP (SeqHaddP s' w (Var i) (Var j') IMP Var j' EQ Var j)))(j::=y)"
    by (metis All_D)
  hence "{OrdP (Var i)} 
         \<turnstile> All j' (SeqHaddP s w (Var i) y IMP (SeqHaddP s' w (Var i) (Var j') IMP Var j' EQ y))"
    using ij by simp
  hence "{OrdP (Var i)} 
         \<turnstile> (SeqHaddP s w (Var i) y IMP (SeqHaddP s' w (Var i) (Var j') IMP Var j' EQ y))(j'::=y')"
    by (metis All_D)
  hence "{OrdP (Var i)} \<turnstile> SeqHaddP s w (Var i) y IMP (SeqHaddP s' w (Var i) y' IMP y' EQ y)"
    using ij by simp
  hence "{} \<turnstile> (OrdP (Var i) IMP SeqHaddP s w (Var i) y IMP (SeqHaddP s' w (Var i) y' IMP y' EQ y))(i::=x)"
    by (metis Imp_I Subst emptyE)
  thus ?thesis
    using ij by simp (metis DisjAssoc2 Disj_commute anti_deduction)
qed (*>*)

lemma HaddP_unique: "{HaddP w x y, HaddP w x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name  where "atom s \<sharp> (w,x,y,y')" "atom s' \<sharp> (w,x,y,y',s)"
    by (metis obtain_fresh)
  hence "{OrdP x, HaddP w x y, HaddP w x y'} \<turnstile> y' EQ y"
    by (auto simp: HaddP.simps [of s _ _ y]  HaddP.simps [of s' _ _ y'] 
             intro: SeqHaddP_unique [THEN cut3])
  thus ?thesis 
    by (metis HaddP_imp_OrdP cut_same thin1)
qed

lemma HaddP_Zero1: assumes "H \<turnstile> OrdP x" shows "H \<turnstile> HaddP Zero x x"
proof -
  fix k::name 
  have "{ OrdP (Var k) } \<turnstile> HaddP Zero (Var k) (Var k)"
    by (rule OrdInd2H [where i=k]) (auto intro: HaddP_Zero2 HaddP_SUCC2 [THEN cut1])
  hence "{} \<turnstile> OrdP (Var k) IMP HaddP Zero (Var k) (Var k)"
    by (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var k) IMP HaddP Zero (Var k) (Var k))(k::=x)"
    by (rule Subst) auto
  hence "{} \<turnstile> OrdP x IMP HaddP Zero x x"
    by simp
  thus ?thesis using assms
    by (metis MP_same thin0)
qed

lemma HaddP_Zero_D1: "insert (HaddP Zero x y) H \<turnstile> x EQ y"
  by (metis Assume HaddP_imp_OrdP HaddP_Zero1 HaddP_unique [THEN cut2] rcut1)

lemma HaddP_Zero_D2: "insert (HaddP x Zero y) H \<turnstile> x EQ y"
  by (metis Assume HaddP_Zero2 HaddP_unique [THEN cut2])

lemma HaddP_SUCC_Ex2:
  assumes "H \<turnstile> HaddP x (SUCC y) z" "atom z' \<sharp> (x,y,z)"
    shows "H \<turnstile> Ex z' (HaddP x y (Var z') AND z EQ SUCC (Var z'))"
proof -
  obtain s::name and s'::name  where "atom s \<sharp> (x,y,z,z')" "atom s' \<sharp> (x,y,z,z',s)"
    by (metis obtain_fresh)
  hence "{ HaddP x (SUCC y) z } \<turnstile> Ex z' (HaddP x y (Var z') AND z EQ SUCC (Var z'))"
    using assms
    apply (auto simp: HaddP.simps [of s _ _ ]  HaddP.simps [of s' _ _ ])
    apply (rule cut_same [OF SeqHaddP_SUCC_lemma [of z']], auto)
    apply (rule Ex_I, auto)+
    done
  thus ?thesis
    by (metis assms(1) cut1)
qed

lemma HaddP_SUCC1: "{ HaddP x y z } \<turnstile> HaddP (SUCC x) y (SUCC z)" (*<*)
proof -
  obtain i::name and j::name and z'::name
   where atoms: "atom i \<sharp> (x,y,z)"  "atom j \<sharp> (i,x,y,z)"  "atom z' \<sharp> (x,i,j)"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> All j (HaddP x (Var i) (Var j) IMP HaddP (SUCC x) (Var i) (SUCC (Var j)))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        using atoms apply auto
        apply (rule cut_same [OF HaddP_Zero_D2])
        apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same], auto intro: HaddP_Zero2)
        done
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms
        apply auto
        apply (rule cut_same [OF HaddP_SUCC_Ex2 [where z'=z']], auto)
        apply (rule Ex_I [where x="Var z'"], auto)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3], simp)
        by (metis Assume HaddP_SUCC2 cut1 thin1)
    qed
  hence "{OrdP (Var i)} \<turnstile> (HaddP x (Var i) (Var j) IMP HaddP (SUCC x) (Var i) (SUCC (Var j)))(j::=z)"
    by (rule All_D)
  hence "{OrdP (Var i)} \<turnstile> HaddP x (Var i) z IMP HaddP (SUCC x) (Var i) (SUCC z)"
    using atoms by auto
  hence "{} \<turnstile> HaddP x (Var i) z IMP HaddP (SUCC x) (Var i) (SUCC z)"
    by (metis HaddP_imp_OrdP Imp_cut)
  hence "{} \<turnstile> (HaddP x (Var i) z IMP HaddP (SUCC x) (Var i) (SUCC z))(i::=y)"
    using atoms by (force intro!: Subst)
  thus ?thesis
    using atoms by simp (metis anti_deduction)
qed (*>*)

lemma HaddP_commute: "{HaddP x y z, OrdP x} \<turnstile> HaddP y x z" (*<*)
proof -
  obtain i::name and j::name and z'::name
   where atoms: "atom i \<sharp> (x,y,z)"  "atom j \<sharp> (i,x,y,z)"  "atom z' \<sharp> (x,i,j)"
    by (metis obtain_fresh)
  have "{OrdP (Var i), OrdP x} \<turnstile> All j (HaddP x (Var i) (Var j) IMP HaddP (Var i) x (Var j))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{OrdP x} \<turnstile> ?scheme(i::=Zero)"
        using atoms apply auto
        apply (rule cut_same [OF HaddP_Zero_D2])
        apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same], auto intro: HaddP_Zero1)
        done
    next
      show "{OrdP x} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms
        apply auto
        apply (rule cut_same [OF HaddP_SUCC_Ex2 [where z'=z']], auto)
        apply (rule Ex_I [where x="Var z'"], auto)
        apply (rule rotate3)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], simp)
        by (metis Assume HaddP_SUCC1 cut1 thin1)
    qed
  hence "{OrdP (Var i), OrdP x} \<turnstile> (HaddP x (Var i) (Var j) IMP HaddP (Var i) x (Var j))(j::=z)"
    by (rule All_D)
  hence "{OrdP (Var i), OrdP x} \<turnstile> HaddP x (Var i) z IMP HaddP (Var i) x z"
    using atoms by auto
  hence "{OrdP x} \<turnstile> HaddP x (Var i) z IMP HaddP (Var i) x z"
    by (metis HaddP_imp_OrdP Imp_cut)
  hence "{OrdP x} \<turnstile> (HaddP x (Var i) z IMP HaddP (Var i) x z)(i::=y)"
    using atoms by (force intro!: Subst)
  thus ?thesis
    using atoms by simp (metis anti_deduction)
qed (*>*)

lemma HaddP_SUCC_Ex1:
  assumes "atom i \<sharp> (x,y,z)"
    shows "insert (HaddP (SUCC x) y z) (insert (OrdP x) H)
           \<turnstile> Ex i (HaddP x y (Var i) AND z EQ SUCC (Var i))"
proof -
  have "{ HaddP (SUCC x) y z, OrdP x } \<turnstile> Ex i (HaddP x y (Var i) AND z EQ SUCC (Var i))"
    apply (rule cut_same [OF HaddP_commute [THEN cut2]])
    apply (blast intro: OrdP_SUCC_I)+
    apply (rule cut_same [OF HaddP_SUCC_Ex2 [where z'=i]], blast)
    using assms apply auto
    apply (auto intro!: Ex_I [where x="Var i"])
    by (metis AssumeH(2) HaddP_commute [THEN cut2] HaddP_imp_OrdP rotate2 thin1)
  thus ?thesis
    by (metis Assume AssumeH(2) cut2)
qed

lemma HaddP_inv2: "{HaddP x y z, HaddP x y' z, OrdP x} \<turnstile> y' EQ y" (*<*)
proof -
  obtain i::name and j::name and u::name and u'::name
   where atoms: "atom i \<sharp> (x,y,y',z)"  "atom j \<sharp> (i,x,y,y',z)"  
                "atom u \<sharp> (x,y,y',i,j)" "atom u' \<sharp> (x,y,y',u,i,j)"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> All j (HaddP (Var i) y (Var j) IMP HaddP (Var i) y' (Var j) IMP y' EQ y)"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        using atoms 
        by auto (metis HaddP_Zero_D1 Sym Trans thin1)
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms
        apply auto
        apply (rule cut_same [OF HaddP_SUCC_Ex1 [where y=y and i=u, THEN cut2]], auto)
        apply (rule Ex_I [where x="Var u"], auto)
        apply (rule cut_same [OF HaddP_SUCC_Ex1 [where y=y' and i=u', THEN cut2]], auto)
        apply (rule cut_same [where A="SUCC (Var u) EQ SUCC (Var u')"])
        apply (auto intro: Sym Trans)
        apply (rule rotate4 [OF ContraProve])
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], force)
        done
    qed
  hence "{OrdP (Var i)} \<turnstile> (HaddP (Var i) y (Var j) IMP HaddP (Var i) y' (Var j) IMP y' EQ y)(j::=z)"
    by (rule All_D)
  hence "{OrdP (Var i)} \<turnstile> HaddP (Var i) y z IMP HaddP (Var i) y' z IMP y' EQ y"
    using atoms by auto
  hence "{} \<turnstile> OrdP (Var i) IMP HaddP (Var i) y z IMP HaddP (Var i) y' z IMP y' EQ y"
    by (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP HaddP (Var i) y z IMP HaddP (Var i) y' z IMP y' EQ y)(i::=x)"
    using atoms by (force intro!: Subst)
  thus ?thesis
    using atoms by simp (metis DisjAssoc2 Disj_commute anti_deduction)
qed (*>*)

lemma Mem_imp_subtract: (*<*)
  assumes "H \<turnstile> x IN y" "H \<turnstile> OrdP y" and k: "atom (k::name) \<sharp> (x,y)"
    shows  "H \<turnstile> Ex k (HaddP x (Var k) y AND Zero IN (Var k))"
proof -
  obtain i::name 
   where atoms: "atom i \<sharp> (x,y,k)" 
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> x IN Var i IMP Ex k (HaddP x (Var k) (Var i) AND Zero IN (Var k))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        by auto
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms k
        apply (auto intro!: Mem_SUCC_EH)
        apply (rule Ex_I [where x="SUCC (Var k)"], auto)
        apply (metis AssumeH(4) HaddP_SUCC2 cut1 insert_commute)
        apply (blast intro: Mem_SUCC_I1)
        apply (rule Ex_I [where x="SUCC Zero"], auto)
        apply (rule thin1)
        apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same], simp)
        apply (metis HaddP_SUCC2 HaddP_Zero2 cut1) 
        apply (rule Ex_I [where x="SUCC (Var k)"], auto intro: Mem_SUCC_I1)
        apply (metis AssumeH(4) HaddP_SUCC2 cut1 insert_commute)
        done
    qed
  hence "{} \<turnstile> OrdP (Var i) IMP x IN Var i IMP Ex k (HaddP x (Var k) (Var i) AND Zero IN (Var k))"
    by (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP x IN Var i IMP Ex k (HaddP x (Var k) (Var i) AND Zero IN (Var k)))(i::=y)"
    by (force intro!: Subst)
  thus ?thesis using assms atoms
    by simp (metis (no_types) anti_deduction cut2)
qed (*>*)

lemma HaddP_OrdP:
  assumes "H \<turnstile> HaddP x y z" "H \<turnstile> OrdP x"  shows "H \<turnstile> OrdP z"  (*<*)
proof -
  obtain i::name and j::name and k::name
   where atoms: "atom i \<sharp> (x,y,z)"  "atom j \<sharp> (i,x,y,z)"  "atom k \<sharp> (i,j,x,y,z)"  
    by (metis obtain_fresh)
  have "{OrdP (Var i), OrdP x} \<turnstile> All j (HaddP x (Var i) (Var j) IMP OrdP (Var j))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{OrdP x} \<turnstile> ?scheme(i::=Zero)"
        using atoms
        by (auto intro: HaddP_Zero_D2 OrdP_cong [THEN Iff_MP_same])
    next
      show "{OrdP x} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms 
        apply auto
        apply (rule cut_same [OF HaddP_SUCC_Ex2 [where z'=k]], auto)
        apply (rule Ex_I [where x="Var k"], auto)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3], auto intro: OrdP_SUCC_I)
        done
    qed
  hence "{OrdP (Var i), OrdP x} \<turnstile> (HaddP x (Var i) (Var j) IMP OrdP (Var j))(j::=z)"
    by (rule All_D)
  hence "{OrdP (Var i), OrdP x} \<turnstile> (HaddP x (Var i) z IMP OrdP z)"
    using atoms by simp
  hence "{OrdP x} \<turnstile> HaddP x (Var i) z IMP OrdP z"
    by (metis HaddP_imp_OrdP Imp_cut)
  hence "{OrdP x} \<turnstile> (HaddP x (Var i) z IMP OrdP z)(i::=y)"
    using atoms by (force intro!: Subst)
  thus ?thesis using assms atoms
    by simp (metis anti_deduction cut2)
qed (*>*)

lemma HaddP_Mem_cancel_left: 
  assumes "H \<turnstile> HaddP x y' z'" "H \<turnstile> HaddP x y z" "H \<turnstile> OrdP x"
    shows "H \<turnstile> z' IN z IFF y' IN y" (*<*)
proof -
  obtain i::name and j::name and j'::name and k::name and k'::name 
   where atoms: "atom i \<sharp> (x,y,y',z,z')" "atom j \<sharp> (i,x,y,y',z,z')" "atom j' \<sharp> (i,j,x,y,y',z,z')"
                 "atom k \<sharp> (i,j,j',x,y,y',z,z')" "atom k' \<sharp> (i,j,j',k,x,y,y',z,z')"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} 
        \<turnstile> All j (All j' (HaddP (Var i) y' (Var j') IMP (HaddP (Var i) y (Var j) IMP
                         ((Var j') IN (Var j) IFF y' IN y))))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        using atoms apply simp
        apply (rule All_I Imp_I Ex_EH)+
        apply (rule cut_same [where A="Var j EQ y"])
        apply (metis HaddP_Zero_D1 Sym)
        apply (rule cut_same [where A="Var j' EQ y'"])
        apply (metis HaddP_Zero_D1 Sym thin1)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], simp)
        apply (rule thin1)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], auto)
        done
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms apply simp
        apply (rule All_I Imp_I Ex_EH)+
        apply (rule cut_same [OF HaddP_SUCC_Ex1 [of k "Var i" y "Var j", THEN cut2]], simp_all)
        apply (rule AssumeH Conj_EH Ex_EH)+
        apply (rule cut_same [OF HaddP_SUCC_Ex1 [of k' "Var i" y' "Var j'", THEN cut2]], simp_all)
        apply (rule AssumeH Conj_EH Ex_EH)+
        apply (rule rotate7)
        apply (rule All_E [where x = "Var k"], simp)
        apply (rule All_E [where x = "Var k'"], simp_all)
        apply (rule Imp_E AssumeH)+
        apply (rule Iff_trans)
        prefer 2
        apply (rule AssumeH)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3], simp)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate5], simp)
        apply (blast intro!: HaddP_OrdP OrdP_IN_SUCC_Iff)
        done
    qed
  hence "{OrdP (Var i)} 
         \<turnstile> (All j' (HaddP (Var i) y' (Var j') IMP (HaddP (Var i) y (Var j) IMP ((Var j') IN (Var j) IFF y' IN y))))(j::=z)"
    by (metis All_D)
  hence "{OrdP (Var i)} 
         \<turnstile> (All j' (HaddP (Var i) y' (Var j') IMP (HaddP (Var i) y z IMP ((Var j') IN z IFF y' IN y))))"
    using atoms by simp
  hence "{OrdP (Var i)} 
         \<turnstile> (HaddP (Var i) y' (Var j') IMP (HaddP (Var i) y z IMP ((Var j') IN z IFF y' IN y)))(j'::=z')"
    by (metis All_D)
  hence "{OrdP (Var i)} \<turnstile> HaddP (Var i) y' z' IMP (HaddP (Var i) y z IMP (z' IN z IFF y' IN y))"
    using atoms by simp
  hence "{} \<turnstile> (OrdP (Var i) IMP HaddP (Var i) y' z' IMP (HaddP (Var i) y z IMP (z' IN z IFF y' IN y)))(i::=x)"
    by (metis Imp_I Subst emptyE)
  thus ?thesis
    using atoms by simp (metis assms MP_null MP_same)
qed (*>*)

lemma HaddP_Mem_cancel_right_Mem: 
  assumes "H \<turnstile> HaddP x' y z'" "H \<turnstile> HaddP x y z" "H \<turnstile> x' IN x" "H \<turnstile> OrdP x"
    shows "H \<turnstile> z' IN z"
proof -
  have "H \<turnstile> OrdP x'"
    by (metis Ord_IN_Ord assms(3) assms(4))
  hence "H \<turnstile> HaddP y x' z'" "H \<turnstile> HaddP y x z"
    by (blast intro: assms HaddP_commute [THEN cut2])+
  thus ?thesis
    by (blast intro: assms HaddP_imp_OrdP [THEN cut1] HaddP_Mem_cancel_left [THEN Iff_MP2_same])
qed

lemma HaddP_Mem_cases:
  assumes "H \<turnstile> HaddP k1 k2 k" "H \<turnstile> OrdP k1" 
          "insert (x IN k1) H \<turnstile> A"
          "insert (Var i IN k2) (insert (HaddP k1 (Var i) x) H) \<turnstile> A"
      and i: "atom (i::name) \<sharp> (k1,k2,k,x,A)" and "\<forall>C \<in> H. atom i \<sharp> C"
    shows "insert (x IN k) H \<turnstile> A" (*<*)
proof -
  obtain j::name where j: "atom j \<sharp> (k1,k2,k,x)"
    by (metis obtain_fresh)
  have seq: "{HaddP k1 k2 k, x IN k, OrdP k1} \<turnstile> x IN k1 OR (Ex i (HaddP k1 (Var i) x AND Var i IN k2))"
    apply (rule cut_same [OF HaddP_OrdP])
    apply (rule AssumeH)+
    apply (rule cut_same [OF Ord_IN_Ord])
    apply (rule AssumeH)+
    apply (rule OrdP_linear [of _ x k1], (rule AssumeH)+)
    proof -
      show "{x IN k1, OrdP x, OrdP k, HaddP k1 k2 k, x IN k, OrdP k1} \<turnstile> x IN k1 OR Ex i (HaddP k1 (Var i) x AND Var i IN k2)"
        by (blast intro: Disj_I1)
    next
      show "{x EQ k1, OrdP x, OrdP k, HaddP k1 k2 k, x IN k, OrdP k1} \<turnstile> x IN k1 OR Ex i (HaddP k1 (Var i) x AND Var i IN k2)"
        apply (rule cut_same [OF Zero_In_OrdP [of k2, THEN cut1]])
        apply (metis AssumeH(4) HaddP_imp_OrdP cut1)
        apply auto
        apply (rule cut_same [where A="HaddP x Zero k"])
        apply (blast intro: HaddP_cong [THEN Iff_MP_same] Sym)
        apply (rule cut_same [where A="x EQ k"])
        apply (metis HaddP_Zero_D2)
        apply (blast intro: Mem_non_refl Mem_cong [THEN Iff_MP_same])
        apply (rule Disj_I2)
        apply (rule Ex_I [where x=Zero])
        using i apply auto
        apply (rule HaddP_cong [THEN Iff_MP_same])
        apply (rule AssumeH Refl HaddP_Zero2)+
        done
    next
      show "{k1 IN x, OrdP x, OrdP k, HaddP k1 k2 k, x IN k, OrdP k1} \<turnstile> x IN k1 OR Ex i (HaddP k1 (Var i) x AND Var i IN k2)"
        apply (rule Disj_I2)
        apply (rule cut_same [OF Mem_imp_subtract [of _ k1 x j]])
        apply (rule AssumeH)+
        using i j apply auto
        apply (rule Ex_I [where x="Var j"], auto intro: HaddP_Mem_cancel_left [THEN Iff_MP_same])
        done
    qed
  show ?thesis using assms
    by (force intro: cut_same [OF seq [THEN cut3]] thin1 simp: insert_commute)
qed (*>*)

lemma HaddP_Mem_contra: 
  assumes "H \<turnstile> HaddP x y z" "H \<turnstile> z IN x" "H \<turnstile> OrdP x"
    shows "H \<turnstile> A"
proof -
  obtain i::name and j::name and k::name
   where atoms: "atom i \<sharp> (x,y,z)" "atom j \<sharp> (i,x,y,z)" "atom k \<sharp> (i,j,x,y,z)" 
    by (metis obtain_fresh)
  have "{OrdP (Var i)}  \<turnstile> All j (HaddP (Var i) y (Var j) IMP Neg ((Var j) IN (Var i)))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        using atoms by auto
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using  atoms apply auto
        apply (rule cut_same [OF HaddP_SUCC_Ex1 [of k "Var i" y "Var j", THEN cut2]], auto)
        apply (rule Ex_I [where x="Var k"], auto)
        apply (blast intro: OrdP_IN_SUCC_D Mem_cong [OF _ Refl, THEN Iff_MP_same])
        done
    qed
  hence "{OrdP (Var i)} \<turnstile> (HaddP (Var i) y (Var j) IMP Neg ((Var j) IN (Var i)))(j::=z)"
    by (metis All_D)
  hence "{} \<turnstile> OrdP (Var i) IMP HaddP (Var i) y z IMP Neg (z IN (Var i))"
    using atoms by simp (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP HaddP (Var i) y z IMP Neg (z IN (Var i)))(i::=x)"
    by (metis Subst emptyE)
  thus ?thesis
    using atoms by simp (metis MP_same MP_null Neg_D assms)
qed (*>*)

lemma exists_HaddP:
  assumes "H \<turnstile> OrdP y" "atom j \<sharp> (x,y)"
    shows "H \<turnstile> Ex j (HaddP x y (Var j))"
proof -
  obtain i::name 
   where atoms: "atom i \<sharp> (j,x,y)" 
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> Ex j (HaddP x (Var i) (Var j))"
       (is "_ \<turnstile> ?scheme")
    proof (rule OrdInd2H)
      show "{} \<turnstile> ?scheme(i::=Zero)"
        using atoms assms
        by (force intro!: Ex_I [where x=x] HaddP_Zero2)
    next
      show "{} \<turnstile> All i (OrdP (Var i) IMP ?scheme IMP ?scheme(i::=SUCC (Var i)))"
        using atoms assms
        apply auto
        apply (auto intro!: Ex_I [where x="SUCC (Var j)"] HaddP_SUCC2)
        apply (metis HaddP_SUCC2 insert_commute thin1)
        done
    qed
  hence "{} \<turnstile> OrdP (Var i) IMP Ex j (HaddP x (Var i) (Var j))"
    by (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP Ex j (HaddP x (Var i) (Var j)))(i::=y)"
    using atoms by (force intro!: Subst)
  thus ?thesis 
    using atoms assms by simp (metis MP_null assms(1))
qed

lemma HaddP_Mem_I: 
  assumes "H \<turnstile> HaddP x y z" "H \<turnstile> OrdP x" shows "H \<turnstile> x IN SUCC z"
proof -
  have "{HaddP x y z, OrdP x} \<turnstile> x IN SUCC z"
    apply (rule OrdP_linear [of _ x "SUCC z"])
    apply (auto intro: OrdP_SUCC_I HaddP_OrdP)
    apply (rule HaddP_Mem_contra, blast)
    apply (metis Assume Mem_SUCC_I2 OrdP_IN_SUCC_D Sym_L thin1 thin2, blast)
    apply (blast intro: HaddP_Mem_contra Mem_SUCC_Refl OrdP_Trans)
    done
  thus ?thesis
    by (rule cut2) (auto intro: assms)
qed


section \<open>A Shifted Sequence\<close>

nominal_function ShiftP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom x \<sharp> (x',y,z,f,del,k); atom x' \<sharp> (y,z,f,del,k); atom y \<sharp> (z,f,del,k); atom z \<sharp> (f,del,g,k)\<rbrakk> \<Longrightarrow>
    ShiftP f k del g =
      All z (Var z IN g IFF 
      (Ex x (Ex x' (Ex y ((Var z) EQ HPair (Var x') (Var y) AND 
                          HaddP del (Var x) (Var x') AND
                          HPair (Var x) (Var y) IN f AND Var x IN k)))))"
by (auto simp: eqvt_def ShiftP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma ShiftP_fresh_iff [simp]: "a \<sharp> ShiftP f k del g \<longleftrightarrow> a \<sharp> f \<and> a \<sharp> k \<and> a \<sharp> del \<and> a \<sharp> g"       
proof -
  obtain x::name and x'::name and y::name and z::name 
    where "atom x \<sharp> (x',y,z,f,del,k)" "atom x' \<sharp> (y,z,f,del,k)" 
          "atom y \<sharp> (z,f,del,k)" "atom z \<sharp> (f,del,g,k)"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma subst_fm_ShiftP [simp]:
  "(ShiftP f k del g)(i::=u) = ShiftP (subst i u f) (subst i u k) (subst i u del) (subst i u g)"
proof -
  obtain x::name and x'::name and y::name and z::name 
  where "atom x \<sharp> (x',y,z,f,del,k,i,u)" "atom x' \<sharp> (y,z,f,del,k,i,u)" 
        "atom y \<sharp> (z,f,del,k,i,u)" "atom z \<sharp> (f,del,g,k,i,u)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: ShiftP.simps [of x x' y z])
qed

lemma ShiftP_Zero: "{} \<turnstile> ShiftP Zero k d Zero"
proof -
  obtain x::name and x'::name and y::name and z::name 
  where "atom x \<sharp> (x',y,z,k,d)" "atom x' \<sharp> (y,z,k,d)" "atom y \<sharp> (z,k,d)" "atom z \<sharp> (k,d)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: ShiftP.simps [of x x' y z])
qed

lemma ShiftP_Mem1:
  "{ShiftP f k del g, HPair a b IN f, HaddP del a a', a IN k} \<turnstile> HPair a' b IN g"       
proof -
  obtain x::name and x'::name and y::name and z::name 
    where "atom x \<sharp> (x',y,z,f,del,k,a,a',b)" "atom x' \<sharp> (y,z,f,del,k,a,a',b)" 
          "atom y \<sharp> (z,f,del,k,a,a',b)" "atom z \<sharp> (f,del,g,k,a,a',b)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: ShiftP.simps [of x x' y z])
    apply (rule All_E [where x="HPair a' b"], auto intro!: Iff_E2)
    apply (rule Ex_I [where x=a], simp)
    apply (rule Ex_I [where x="a'"], simp)
    apply (rule Ex_I [where x=b], auto intro: Mem_Eats_I1)
    done
qed
 
lemma ShiftP_Mem2:
  assumes "atom u \<sharp> (f,k,del,a,b)"
  shows  "{ShiftP f k del g, HPair a b IN g} \<turnstile> Ex u ((Var u) IN k AND HaddP del (Var u) a AND HPair (Var u) b IN f)"       
proof -
  obtain x::name and x'::name and y::name and z::name 
  where atoms: "atom x \<sharp> (x',y,z,f,del,g,k,a,u,b)" "atom x' \<sharp> (y,z,f,del,g,k,a,u,b)" 
               "atom y \<sharp> (z,f,del,g,k,a,u,b)" "atom z \<sharp> (f,del,g,k,a,u,b)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (auto simp: ShiftP.simps [of x x' y z])
    apply (rule All_E [where x="HPair a b"])
    apply (auto intro!: Iff_E1 [OF Assume]) 
    apply (rule Ex_I [where x="Var x"])
    apply (auto intro: Mem_cong [OF HPair_cong Refl, THEN Iff_MP2_same])
    apply (blast intro: HaddP_cong [OF Refl Refl, THEN Iff_MP2_same])
    done
qed

lemma ShiftP_Mem_D:
  assumes "H \<turnstile> ShiftP f k del g" "H \<turnstile> a IN g"
          "atom x \<sharp> (x',y,a,f,del,k)" "atom x' \<sharp> (y,a,f,del,k)" "atom y \<sharp> (a,f,del,k)"
  shows  "H \<turnstile> (Ex x (Ex x' (Ex y (a EQ HPair (Var x') (Var y) AND 
                                  HaddP del (Var x) (Var x') AND
                                  HPair (Var x) (Var y) IN f AND Var x IN k))))" 
         (is "_ \<turnstile> ?concl")
proof -
  obtain z::name where "atom z \<sharp> (x,x',y,f,del,g,k,a)"
    by (metis obtain_fresh)
  hence "{ShiftP f k del g, a IN g} \<turnstile> ?concl" using assms
    by (auto simp: ShiftP.simps [of x x' y z]) (rule All_E [where x=a], auto intro: Iff_E1)
  thus ?thesis
    by (rule cut2) (rule assms)+ 
qed

lemma ShiftP_Eats_Eats: 
  "{ShiftP f k del g, HaddP del a a', a IN k} 
   \<turnstile> ShiftP (Eats f (HPair a b)) k del (Eats g (HPair a' b))" (*<*)
proof -
  obtain x::name and x'::name and y::name and z::name 
    where "atom x \<sharp> (x',y,z,f,del,g,k,a,a',b)" "atom x' \<sharp> (y,z,f,del,g,k,a,a',b)" 
          "atom y \<sharp> (z,f,del,g,k,a,a',b)" "atom z \<sharp> (f,del,g,k,a,a',b)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: ShiftP.simps [of x x' y z] intro!: Iff_I [THEN Swap])
    apply (rule All_E [where x="Var z", THEN rotate2], simp)
    apply (rule Iff_E)
    apply auto [1]
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (blast intro: Mem_Eats_I1, blast)
    apply (rule Ex_I [where x=a], simp)
    apply (rule Ex_I [where x="a'"], simp)
    apply (rule Ex_I [where x=b], simp)
    apply (metis Assume AssumeH(3) AssumeH(4) Conj_I Mem_Eats_I2 Refl)
    apply (rule All_E [where x="Var z", THEN rotate5], auto)
    apply (rule Mem_Eats_I1)
    apply (rule Iff_MP2_same [OF Hyp], blast)
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"], auto)
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate5], simp)
    apply (blast intro: Mem_Eats_I2 HaddP_cong [THEN Iff_MP_same] HaddP_unique [THEN cut2] HPair_cong)
    done
qed (*>*)

lemma ShiftP_Eats_Neg: 
  assumes "atom u \<sharp> (u',v,f,k,del,g,c)" "atom u' \<sharp> (v,f,k,del,g,c)" "atom v \<sharp> (f,k,del,g,c)"
  shows
  "{ShiftP f k del g, 
    Neg (Ex u (Ex u' (Ex v (c EQ HPair (Var u) (Var v) AND Var u IN k AND HaddP del (Var u) (Var u')))))} 
   \<turnstile> ShiftP (Eats f c) k del g"  (*<*)
proof -
  obtain x::name and x'::name and y::name and z::name 
  where atoms: "atom x \<sharp> (x',y,z,u,u',v,f,k,del,g,c)" "atom x' \<sharp> (y,z,u,u',v,f,k,del,g,c)" 
               "atom y \<sharp> (z,u,u',v,f,k,del,g,c)" "atom z \<sharp> (u,u',v,f,k,del,g,c)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (auto simp: ShiftP.simps [of x x' y z] intro!: Iff_I [THEN Swap])
    apply (rule All_E [where x="Var z", THEN rotate3])
    apply (auto intro!: Iff_E1 [OF Assume]) 
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (blast intro: Mem_Eats_I1)
    apply (rule All_E [where x="Var z", THEN rotate6], simp)
    apply (rule Iff_E2)
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"])
    apply (auto intro: Mem_Eats_I1)
    apply (rule Swap [THEN rotate5])
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (blast intro: Sym Mem_Eats_I1)
    done
qed (*>*)

lemma exists_ShiftP:
  assumes t: "atom t \<sharp> (s,k,del)"
  shows "H \<turnstile> Ex t (ShiftP s k del (Var t))" (*<*)
proof -
  obtain i::name and j::name
    where i: "atom (i::name) \<sharp> (s,t,k,del)" and j: "atom (j::name) \<sharp> (i,s,t,k,del)" 
    by (metis obtain_fresh) 
  have "{} \<turnstile> Ex t (ShiftP (Var i) k del (Var t))" (is "{} \<turnstile> ?scheme")
  proof (rule Ind [of j])
    show "atom j \<sharp> (i, ?scheme)" using j
      by simp 
  next
    show "{} \<turnstile> ?scheme(i::=Zero)" using i t
      by (auto intro!: Ex_I [where x=Zero] simp: ShiftP_Zero)
  next
    obtain x::name and x'::name and y::name 
    where atoms: "atom x \<sharp> (x',y,s,k,del,t,i,j)" "atom x' \<sharp> (y,s,k,del,t,i,j)" 
                 "atom y \<sharp> (s,k,del,t,i,j)" 
      by (metis obtain_fresh)
    let ?caseA = "Ex x (Ex x' (Ex y ((Var j) EQ HPair (Var x) (Var y) AND Var x IN k AND 
                                     HaddP del (Var x) (Var x'))))"
    show "{} \<turnstile> All i (All j (?scheme IMP ?scheme(i::=Var j) IMP ?scheme(i::=Eats (Var i) (Var j))))"
      using i j atoms
      apply (auto del: Ex_EH)
      apply (rule Ex_E)
      apply (auto del: Ex_EH)
      apply (rule Ex_E)
      apply (auto del: Ex_EH)
      apply (rule thin1, auto)
      proof (rule Cases [where A="?caseA"]) 
        show "{?caseA, ShiftP (Var i) k del (Var t)} 
              \<turnstile> Ex t (ShiftP (Eats (Var i) (Var j)) k del (Var t))"
          using i j t atoms
          apply (auto simp del: ShiftP.simps)
          apply (rule Ex_I [where x="Eats (Var t) (HPair (Var x') (Var y))"], auto)
          apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3])
          apply (auto intro: ShiftP_Eats_Eats [THEN cut3])
          done
      next
        show "{Neg ?caseA, ShiftP (Var i) k del (Var t)} 
              \<turnstile> Ex t (ShiftP (Eats (Var i) (Var j)) k del (Var t))"
          using atoms
          by (auto intro!: Ex_I [where x="Var t"] ShiftP_Eats_Neg [of x x' y, THEN cut2] 
                   simp: ShiftP_Zero)
      qed
  qed
  hence "{} \<turnstile> (Ex t (ShiftP (Var i) k del (Var t)))(i::=s)"
    by (blast intro: Subst)
  thus ?thesis using i t 
    by (auto intro: thin0)
qed (*>*)


section \<open>Union of Two Sets\<close>

nominal_function UnionP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "atom i \<sharp> (x,y,z) \<Longrightarrow> UnionP x y z = All i (Var i IN z IFF (Var i IN x OR Var i IN y))"
by (auto simp: eqvt_def UnionP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma UnionP_fresh_iff [simp]: "a \<sharp> UnionP x y z \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y \<and> a \<sharp> z"
proof -
  obtain i::name where "atom i \<sharp> (x,y,z)"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma subst_fm_UnionP [simp]:
  "(UnionP x y z)(i::=u) = UnionP (subst i u x) (subst i u y) (subst i u z)"
proof -
  obtain j::name where "atom j \<sharp> (x,y,z,i,u)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: UnionP.simps [of j])
qed

lemma Union_Zero1: "H \<turnstile> UnionP Zero x x"
proof -
  obtain i::name where "atom i \<sharp> x"
    by (metis obtain_fresh)
  hence "{} \<turnstile> UnionP Zero x x"
    by (auto simp: UnionP.simps [of i] intro: Disj_I2)
  thus ?thesis
    by (metis thin0)
qed

lemma Union_Eats: "{UnionP x y z} \<turnstile> UnionP (Eats x a) y (Eats z a)"
proof -
  obtain i::name where "atom i \<sharp> (x,y,z,a)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: UnionP.simps [of i])
    apply (rule Ex_I [where x="Var i"])
    apply (auto intro: Iff_E1 [THEN rotate2] Iff_E2 [THEN rotate2] Mem_Eats_I1 Mem_Eats_I2 Disj_I1 Disj_I2)
    done
qed

lemma exists_Union_lemma: 
  assumes z: "atom z \<sharp> (i,y)" and i: "atom i \<sharp> y"
  shows "{} \<turnstile> Ex z (UnionP (Var i) y (Var z))"
proof -
  obtain j::name where j: "atom j \<sharp> (y,z,i)"
    by (metis obtain_fresh) 
  show "{} \<turnstile> Ex z (UnionP (Var i) y (Var z))"
    apply (rule Ind [of j i]) using j z i
    apply simp_all
    apply (rule Ex_I [where x=y], simp add: Union_Zero1)
    apply (auto del: Ex_EH)
    apply (rule Ex_E)
    apply (rule NegNeg_E)
    apply (rule Ex_E)
    apply (auto del: Ex_EH)
    apply (rule thin1, force intro: Ex_I [where x="Eats (Var z) (Var j)"] Union_Eats)
    done
qed    

lemma exists_UnionP: 
  assumes z: "atom z \<sharp> (x,y)"  shows "H \<turnstile> Ex z (UnionP x y (Var z))"
proof -
  obtain i::name  where i: "atom i \<sharp> (y,z)"
    by (metis obtain_fresh) 
  hence "{} \<turnstile> Ex z (UnionP (Var i) y (Var z))"
    by (metis exists_Union_lemma fresh_Pair fresh_at_base(2) z)
  hence "{} \<turnstile> (Ex z (UnionP (Var i) y (Var z)))(i::=x)"
    by (metis Subst empty_iff)
  thus ?thesis using i z
    by (simp add: thin0)
qed

lemma UnionP_Mem1: "{ UnionP x y z, a IN x } \<turnstile> a IN z"
proof -
  obtain i::name where "atom i \<sharp> (x,y,z,a)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp: UnionP.simps [of i] intro: All_E [where x=a] Disj_I1 Iff_E2)
qed

lemma UnionP_Mem2: "{ UnionP x y z, a IN y } \<turnstile> a IN z"
proof -
  obtain i::name where "atom i \<sharp> (x,y,z,a)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp: UnionP.simps [of i] intro: All_E [where x=a] Disj_I2 Iff_E2)
qed

lemma UnionP_Mem: "{ UnionP x y z, a IN z } \<turnstile> a IN x OR a IN y"
proof -
  obtain i::name where "atom i \<sharp> (x,y,z,a)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp: UnionP.simps [of i] intro: All_E [where x=a] Iff_E1)
qed

lemma UnionP_Mem_E:
  assumes "H \<turnstile> UnionP x y z"
      and "insert (a IN x) H \<turnstile> A"
      and "insert (a IN y) H \<turnstile> A"
    shows "insert (a IN z) H \<turnstile> A"
  using assms
  by (blast intro: rotate2 cut_same [OF UnionP_Mem [THEN cut2]] thin1) 

  
section \<open>Append on Sequences\<close>

nominal_function SeqAppendP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom g1 \<sharp> (g2,f1,k1,f2,k2,g); atom g2 \<sharp> (f1,k1,f2,k2,g)\<rbrakk> \<Longrightarrow>
    SeqAppendP f1 k1 f2 k2 g =
      (Ex g1 (Ex g2 (RestrictedP f1 k1 (Var g1) AND 
                     ShiftP f2 k2 k1 (Var g2) AND 
                     UnionP (Var g1) (Var g2) g)))"
by (auto simp: eqvt_def SeqAppendP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma SeqAppendP_fresh_iff [simp]: 
  "a \<sharp> SeqAppendP f1 k1 f2 k2 g \<longleftrightarrow> a \<sharp> f1 \<and> a \<sharp> k1 \<and> a \<sharp> f2 \<and> a \<sharp> k2 \<and> a \<sharp> g"       
proof -
  obtain g1::name and g2::name
    where "atom g1 \<sharp> (g2,f1,k1,f2,k2,g)" "atom g2 \<sharp> (f1,k1,f2,k2,g)"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma subst_fm_SeqAppendP [simp]:
  "(SeqAppendP f1 k1 f2 k2 g)(i::=u) = 
   SeqAppendP (subst i u f1) (subst i u k1) (subst i u f2) (subst i u k2) (subst i u g)"
proof -
  obtain g1::name and g2::name 
  where "atom g1 \<sharp> (g2,f1,k1,f2,k2,g,i,u)" "atom g2 \<sharp> (f1,k1,f2,k2,g,i,u)" 
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqAppendP.simps [of g1 g2])
qed

lemma exists_SeqAppendP:
  assumes "atom g \<sharp> (f1,k1,f2,k2)"
  shows "H \<turnstile> Ex g (SeqAppendP f1 k1 f2 k2 (Var g))"
proof -
  obtain g1::name and g2::name
  where atoms: "atom g1 \<sharp> (g2,f1,k1,f2,k2,g)" "atom g2 \<sharp> (f1,k1,f2,k2,g)"
    by (metis obtain_fresh)
  hence "{} \<turnstile> Ex g (SeqAppendP f1 k1 f2 k2 (Var g))"
    using assms
    apply (auto simp: SeqAppendP.simps [of g1 g2])
    apply (rule cut_same [OF exists_RestrictedP [of g1 f1 k1]], auto)
    apply (rule cut_same [OF exists_ShiftP [of g2 f2 k2 k1]], auto)
    apply (rule cut_same [OF exists_UnionP [of g "Var g1" "Var g2"]], auto)
    apply (rule Ex_I [where x="Var g"], simp)
    apply (rule Ex_I [where x="Var g1"], simp)
    apply (rule Ex_I [where x="Var g2"], auto)
    done
  thus ?thesis using assms
    by (metis thin0)
qed

lemma SeqAppendP_Mem1: "{SeqAppendP f1 k1 f2 k2 g, HPair x y IN f1, x IN k1} \<turnstile> HPair x y IN g"
proof -
  obtain g1::name and g2::name
    where "atom g1 \<sharp> (g2,f1,k1,f2,k2,g,x,y)" "atom g2 \<sharp> (f1,k1,f2,k2,g,x,y)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqAppendP.simps [of g1 g2] intro: UnionP_Mem1 [THEN cut2] RestrictedP_Mem [THEN cut3])
qed

lemma SeqAppendP_Mem2: "{SeqAppendP f1 k1 f2 k2 g, HaddP k1 x x', x IN k2, HPair x y IN f2} \<turnstile> HPair x' y IN g"
proof -
  obtain g1::name and g2::name
    where "atom g1 \<sharp> (g2,f1,k1,f2,k2,g,x,x',y)" "atom g2 \<sharp> (f1,k1,f2,k2,g,x,x',y)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqAppendP.simps [of g1 g2] intro: UnionP_Mem2 [THEN cut2] ShiftP_Mem1 [THEN cut4])
qed

lemma SeqAppendP_Mem_E: 
  assumes "H \<turnstile> SeqAppendP f1 k1 f2 k2 g" 
      and "insert (HPair x y IN f1) (insert (x IN k1) H) \<turnstile> A" 
      and "insert (HPair (Var u) y IN f2) (insert (HaddP k1 (Var u) x) (insert (Var u IN k2) H)) \<turnstile> A"
      and u: "atom u \<sharp> (f1,k1,f2,k2,x,y,g,A)" "\<forall>C \<in> H. atom u \<sharp> C"
  shows "insert (HPair x y IN g) H \<turnstile> A" (*<*)
proof -
  obtain g1::name and g2::name
  where atoms: "atom g1 \<sharp> (g2,f1,k1,f2,k2,g,x,y,u)" "atom g2 \<sharp> (f1,k1,f2,k2,g,x,y,u)"
    by (metis obtain_fresh)
  hence "{SeqAppendP f1 k1 f2 k2 g, HPair x y IN g} 
         \<turnstile> (HPair x y IN f1 AND x IN k1) OR Ex u ((Var u) IN k2 AND HaddP k1 (Var u) x AND HPair (Var u) y IN f2)"
    using u
    apply (auto simp: SeqAppendP.simps [of g1 g2])
    apply (rule UnionP_Mem_E [THEN rotate4])
    apply (rule AssumeH)+
    apply (blast intro: Disj_I1 cut_same [OF RestrictedP_Mem2 [THEN cut2]])
    apply (rule Disj_I2)
    apply (rule cut_same [OF ShiftP_Mem2 [where u=u, THEN cut2]])
    defer 1
    apply force+
    done
  thus ?thesis 
    apply (rule cut_same [OF _ [THEN cut2]])
    using assms
    apply (auto intro: thin1 rotate2 thin3 thin4)
    done
qed (*>*)

section \<open>LstSeqP and SeqAppendP\<close>

lemma HDomain_Incl_SeqAppendP:  \<comment> \<open>The And eliminates the need to prove @{text cut5}\<close>
  "{SeqAppendP f1 k1 f2 k2 g, HDomain_Incl f1 k1 AND HDomain_Incl f2 k2, 
    HaddP k1 k2 k, OrdP k1} \<turnstile> HDomain_Incl g k" (*<*)
proof -
  obtain x::name and y::name and z::name and i::name 
    where "atom x \<sharp> (f1,k1,f2,k2,g,k,y,z,i)"  "atom y \<sharp> (f1,k1,f2,k2,g,k,z,i)"  
          "atom z \<sharp> (f1,k1,f2,k2,g,k,i)"  "atom i \<sharp> (f1,k1,f2,k2,g,k)"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (auto simp: HDomain_Incl.simps [of x _ _ y z])
    apply (rule HaddP_Mem_cases [where i=i, THEN rotate2], auto)
    \<comment> \<open>case 1\<close>
    apply (rule All_E' [where x = "Var x"], blast, auto)
    apply (rule ContraProve [THEN rotate4])
    apply (rule Ex_I [where x = "Var y"], auto)
    apply (rule Ex_I [where x = "Var z"], auto)
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate2], simp)
    apply (rule SeqAppendP_Mem1 [THEN cut3], auto)
    apply (rule Mem_cong [OF Assume Refl, THEN Iff_MP_same], auto)
    \<comment> \<open>case 2\<close>
    apply (rule Ex_I [where x = "Var i"], auto)
    apply (rule ContraProve [THEN rotate5])
    apply (rule Ex_I [where x = "Var y"], simp)
    apply (rule Ex_I [where x = "HPair (Var x) (Var y)"], auto)
    apply (blast intro: SeqAppendP_Mem2 [THEN cut4] Mem_cong [OF _ Refl, THEN Iff_MP_same])
    done
qed (*>*)

declare SeqAppendP.simps [simp del]

lemma HFun_Sigma_SeqAppendP:
  "{SeqAppendP f1 k1 f2 k2 g, HFun_Sigma f1, HFun_Sigma f2, OrdP k1} \<turnstile> HFun_Sigma g" (*<*)
proof -
  obtain x::name and y::name and z::name 
     and x'::name and y'::name and z'::name and g1::name and g2::name
     and v::name and v'::name and w::name
    where atoms: 
       "atom v \<sharp> (v',w,g1,g2,z,z',x,y,x',y',f1,k1,f2,k2,g)" "atom v' \<sharp> (w,g1,g2,z,z',x,y,x',y',f1,k1,f2,k2,g)"
       "atom w \<sharp> (g1,g2,z,z',x,y,x',y',f1,k1,f2,k2,g)" 
       "atom g1 \<sharp> (g2,z,z',x,y,x',y',f1,k1,f2,k2,g)" "atom g2 \<sharp> (z,z',x,y,x',y',f1,k1,f2,k2,g)"
       "atom z \<sharp> (z',x,y,x',y',f1,k1,f2,k2,g)" "atom z' \<sharp> (x,y,x',y',f1,k1,f2,k2,g)"
       "atom x \<sharp> (y,x',y',f1,k1,f2,k2,g)" "atom y \<sharp> (x',y',f1,k1,f2,k2,g)" 
       "atom x' \<sharp> (y',f1,k1,f2,k2,g)" "atom y' \<sharp> (f1,k1,f2,k2,g)" 
    by (metis obtain_fresh) 
  thus ?thesis
    apply (simp add: HFun_Sigma.simps [of z g z' x y x' y'] SeqAppendP.simps [of g1 g2])
    apply (rule Ex_EH Conj_EH All_I Imp_I)+
    apply (rule cut_same [OF UnionP_Mem [where a = "Var z", THEN cut2]])
    apply (rule AssumeH)+
    apply (rule Disj_E)
    apply (rule cut_same [OF UnionP_Mem [where a = "Var z'", THEN cut2]])
    apply (rule AssumeH)+
    apply (rule thin1 [where A="UnionP (Var g1) (Var g2) g", THEN rotate6])
    apply (rule Disj_E)
    \<comment> \<open>case 1/1\<close>
    apply (rule thin1 [where A="ShiftP f2 k2 k1 (Var g2)", THEN rotate5])
    apply (rule RestrictedP_Mem_D [where a = "Var z"])
    apply (rule AssumeH)+
    apply (rule RestrictedP_Mem_D [where a = "Var z'"])
    apply (rule AssumeH)+
    apply (simp add: HFun_Sigma.simps [of z f1 z' x y x' y'])
    apply (rule All2_E [where x = "Var z", THEN rotate8], simp_all, blast)
    apply (rule All2_E [where x = "Var z'"], simp_all, blast)
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y'"], simp)
    apply (rule Conj_I, blast)+
    apply blast
    \<comment> \<open>case 1/2\<close>
    apply (rule RestrictedP_Mem_D [where a = "Var z"])
    apply (rule AssumeH)+
    apply (rule thin1 [where A="Var z IN g", THEN rotate5])
    apply (rule thin1 [where A="Var z' IN g", THEN rotate4])
    apply (rule cut_same [OF HFun_Sigma_Mem_imp_HPair [of _ f1 "Var z" x y]], simp_all)
    apply (rule AssumeH)+
    apply (rule cut_same [OF ShiftP_Mem_D [where x=v and x'=v' and y=w]])
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply auto [3]
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (rule Ex_I [where x="Var v'"], simp)
    apply (rule Ex_I [where x="Var w"], simp)
    apply auto [1]
    apply (blast intro: Mem_HFun_Sigma_OrdP [THEN cut2] Mem_cong [OF _ Refl, THEN Iff_MP_same])
    apply (blast intro: Hyp HaddP_OrdP)
    apply (rule cut_same [OF RestrictedP_Mem2 [THEN cut2]])
    apply (rule AssumeH)+
    apply (blast intro: Mem_cong [OF _ Refl, THEN Iff_MP_same])
    apply (blast intro: Hyp Mem_cong [OF _ Refl, THEN Iff_MP_same] HaddP_Mem_contra)
    \<comment> \<open>END of case 1/2\<close>
    apply (rule cut_same [OF UnionP_Mem [where a = "Var z'", THEN cut2]])
    apply (rule AssumeH)+
    apply (rule thin1 [where A="UnionP (Var g1) (Var g2) g", THEN rotate6])
    apply (rule Disj_E)
    \<comment> \<open>case 2/1\<close>
    apply (rule RestrictedP_Mem_D [where a = "Var z'"])
    apply (rule AssumeH)+
    apply (rule thin1 [where A="Var z IN g", THEN rotate5])
    apply (rule thin1 [where A="Var z' IN g", THEN rotate4])
    apply (rule cut_same [OF HFun_Sigma_Mem_imp_HPair [of _ f1 "Var z'" x y]], simp_all)
    apply (rule AssumeH)+
    apply (rule cut_same [OF ShiftP_Mem_D [where x=v and x'=v' and y=w]])
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply auto [3]
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x="Var v'"], simp)
    apply (rule Ex_I [where x="Var w"], simp)
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply auto [1]
    apply (blast intro: Hyp HaddP_OrdP)
    apply (blast intro: Mem_HFun_Sigma_OrdP [THEN cut2] Mem_cong [OF _ Refl, THEN Iff_MP_same])
    apply (rule cut_same [OF RestrictedP_Mem2 [THEN cut2]])
    apply (rule AssumeH)+
    apply (blast intro: Mem_cong [OF _ Refl, THEN Iff_MP_same])
    apply (blast intro: Mem_cong [OF _ Refl, THEN Iff_MP2_same] HaddP_Mem_contra Hyp)
    \<comment> \<open>case 2/2\<close>
    apply (rule cut_same [OF ShiftP_Mem_D [where x=x and x'=x' and y=y and a = "Var z"]])
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply simp_all
    apply (rule cut_same [OF ShiftP_Mem_D [where x=v and x'=v' and y=w and a = "Var z'"]])
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply simp_all
    apply (rule thin1 [where A="ShiftP f2 k2 k1 (Var g2)", THEN rotate7])
    apply (rule thin1 [where A="RestrictedP f1 k1 (Var g1)", THEN rotate7])
    apply (rule AssumeH Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x="Var x'"], simp)
    apply (rule Ex_I [where x="Var y"], simp)
    apply (rule Ex_I [where x="Var v'"], simp)
    apply (rule Ex_I [where x="Var w"], auto intro: Hyp HaddP_OrdP)
    apply (rule cut_same [where A="Var x EQ Var v"])
    apply (blast intro: HaddP_inv2 [THEN cut3] HaddP_cong [OF Refl Refl, THEN Iff_MP_same] Hyp)
    apply (rule HFun_Sigma_E [where r=f2])
    apply (auto intro: Hyp Var_Eq_subst_Iff [THEN Iff_MP_same])
    done
qed (*>*)

lemma LstSeqP_SeqAppendP:
  assumes "H \<turnstile> SeqAppendP f1 (SUCC k1) f2 (SUCC k2) g"
          "H \<turnstile> LstSeqP f1 k1 y1" "H \<turnstile> LstSeqP f2 k2 y2" "H \<turnstile> HaddP k1 k2 k" 
  shows "H \<turnstile> LstSeqP g (SUCC k) y2"
proof -
  have "{SeqAppendP f1 (SUCC k1) f2 (SUCC k2) g, LstSeqP f1 k1 y1, LstSeqP f2 k2 y2, HaddP k1 k2 k} 
   \<turnstile> LstSeqP g (SUCC k) y2"
    apply (auto simp: LstSeqP.simps intro: HaddP_OrdP OrdP_SUCC_I)
    apply (rule HDomain_Incl_SeqAppendP [THEN cut4])
    apply (rule AssumeH Conj_I)+
    apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
    apply (blast intro: HaddP_OrdP OrdP_SUCC_I)
    apply (rule HFun_Sigma_SeqAppendP [THEN cut4])
    apply (auto intro: HaddP_OrdP OrdP_SUCC_I)
    apply (blast intro: Mem_SUCC_Refl HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1] 
                        SeqAppendP_Mem2 [THEN cut4])
    done
  thus ?thesis using assms
    by (rule cut4)
qed

lemma SeqAppendP_NotInDom: "{SeqAppendP f1 k1 f2 k2 g, HaddP k1 k2 k, OrdP k1} \<turnstile> NotInDom k g"
proof -
  obtain x::name and z::name 
    where "atom x \<sharp> (z,f1,k1,f2,k2,g,k)"  "atom z \<sharp> (f1,k1,f2,k2,g,k)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: NotInDom.simps [of z])
    apply (rule SeqAppendP_Mem_E [where u=x])
    apply (rule AssumeH)+
    apply (blast intro: HaddP_Mem_contra, simp_all)
    apply (rule cut_same [where A="(Var x) EQ k2"])
    apply (blast intro: HaddP_inv2 [THEN cut3])
    apply (blast intro: Mem_non_refl [where x=k2] Mem_cong [OF _ Refl, THEN Iff_MP_same])
    done
qed

lemma LstSeqP_SeqAppendP_Eats:
  assumes "H \<turnstile> SeqAppendP f1 (SUCC k1) f2 (SUCC k2) g"
          "H \<turnstile> LstSeqP f1 k1 y1" "H \<turnstile> LstSeqP f2 k2 y2" "H \<turnstile> HaddP k1 k2 k" 
  shows "H \<turnstile> LstSeqP (Eats g (HPair (SUCC (SUCC k)) z)) (SUCC (SUCC k)) z"
proof -
  have "{SeqAppendP f1 (SUCC k1) f2 (SUCC k2) g, LstSeqP f1 k1 y1, LstSeqP f2 k2 y2, HaddP k1 k2 k} 
        \<turnstile> LstSeqP (Eats g (HPair (SUCC (SUCC k)) z)) (SUCC (SUCC k)) z"
    apply (rule cut2 [OF NotInDom_LstSeqP_Eats]) 
    apply (rule SeqAppendP_NotInDom [THEN cut3])
    apply (rule AssumeH)
    apply (metis HaddP_SUCC1 HaddP_SUCC2 cut1 thin1)
    apply (metis Assume LstSeqP_OrdP OrdP_SUCC_I insert_commute)
    apply (blast intro: LstSeqP_SeqAppendP)
    done
  thus ?thesis using assms
    by (rule cut4)
qed

section \<open>Substitution and Abstraction on Terms\<close>

subsection \<open>Atomic cases\<close>

lemma SeqStTermP_Var_same:
  assumes "atom s \<sharp> (k,v,i)" "atom k \<sharp> (v,i)"
    shows "{VarP v} \<turnstile> Ex s (Ex k (SeqStTermP v i v i (Var s) (Var k)))"
proof -
  obtain l::name and sl::name and sl'::name and m::name and sm::name and sm'::name
     and n::name and sn::name and sn'::name
    where "atom l \<sharp> (v,i,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,i,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,i,s,k,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (v,i,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,i,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,i,s,k,sm',sn,sn')" "atom sm' \<sharp> (v,i,s,k,sn,sn')"
          "atom sn \<sharp> (v,i,s,k,sn')" "atom sn' \<sharp> (v,i,s,k)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqStTermP.simps [of l _ _ v i sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair v i))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = v], simp)
    apply (rule Ex_I [where x = i], auto intro: Disj_I1 Mem_Eats_I2 HPair_cong)
    done
qed

lemma SeqStTermP_Var_diff:
  assumes "atom s \<sharp> (k,v,w,i)" "atom k \<sharp> (v,w,i)"
    shows "{VarP v, VarP w, Neg (v EQ w) } \<turnstile> Ex s (Ex k (SeqStTermP v i w w (Var s) (Var k)))"
proof -
  obtain l::name and sl::name and sl'::name and m::name and sm::name and sm'::name
     and n::name and sn::name and sn'::name
    where "atom l \<sharp> (v,w,i,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,w,i,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,w,i,s,k,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (v,w,i,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,w,i,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,w,i,s,k,sm',sn,sn')" "atom sm' \<sharp> (v,w,i,s,k,sn,sn')"
          "atom sn \<sharp> (v,w,i,s,k,sn')" "atom sn' \<sharp> (v,w,i,s,k)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqStTermP.simps [of l _ _ v i sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair w w))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule rotate2 [OF Swap])
    apply (rule Ex_I [where x = w], simp)
    apply (rule Ex_I [where x = w], auto simp: VarP_def)
    apply (blast intro: HPair_cong Mem_Eats_I2)
    apply (blast intro: Sym OrdNotEqP_I Disj_I1 Disj_I2)
    done
qed

lemma SeqStTermP_Zero:
  assumes "atom s \<sharp> (k,v,i)" "atom k \<sharp> (v,i)"
    shows "{VarP v} \<turnstile> Ex s (Ex k (SeqStTermP v i Zero Zero (Var s) (Var k)))" (*<*)
proof -
  obtain l::name and sl::name and sl'::name and m::name and sm::name and sm'::name
     and n::name and sn::name and sn'::name
    where "atom l \<sharp> (v,i,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,i,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,i,s,k,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (v,i,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,i,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,i,s,k,sm',sn,sn')" "atom sm' \<sharp> (v,i,s,k,sn,sn')"
          "atom sn \<sharp> (v,i,s,k,sn')" "atom sn' \<sharp> (v,i,s,k)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqStTermP.simps [of l _ _ v i sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair Zero Zero))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = Zero], simp)
    apply (rule Ex_I [where x = Zero], simp)
    apply (rule Conj_I)
    apply (force intro: Var_Eq_subst_Iff [THEN Iff_MP_same] Mem_Eats_I2)
    apply (force simp: VarP_def OrdNotEqP.simps intro: Disj_I1 Disj_I2)
    done
qed (*>*)

corollary SubstTermP_Zero: "{TermP t} \<turnstile> SubstTermP \<lceil>Var v\<rceil> t Zero Zero"
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,t,k)"  "atom k \<sharp> (v,t)"
    by (metis obtain_fresh)
  thus ?thesis 
    by (auto simp: SubstTermP.simps [of s _ _ _ _ k] intro: SeqStTermP_Zero [THEN cut1])
qed

corollary SubstTermP_Var_same: "{VarP v, TermP t} \<turnstile> SubstTermP v t v t"
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,t,k)" "atom k \<sharp> (v,t)"
    by (metis obtain_fresh)
  thus ?thesis 
    by (auto simp: SubstTermP.simps [of s _ _ _ _ k] intro: SeqStTermP_Var_same [THEN cut1])
qed

corollary SubstTermP_Var_diff: "{VarP v, VarP w, Neg (v EQ w), TermP t} \<turnstile> SubstTermP v t w w"
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,w,t,k)" "atom k \<sharp> (v,w,t)"
    by (metis obtain_fresh)
  thus ?thesis 
    by (auto simp: SubstTermP.simps [of s _ _ _ _ k] intro: SeqStTermP_Var_diff [THEN cut3])
qed

lemma SeqStTermP_Ind:
  assumes "atom s \<sharp> (k,v,t,i)" "atom k \<sharp> (v,t,i)"
    shows "{VarP v, IndP t} \<turnstile> Ex s (Ex k (SeqStTermP v i t t (Var s) (Var k)))"
proof -
  obtain l::name and sl::name and sl'::name and m::name and sm::name and sm'::name
     and n::name and sn::name and sn'::name
    where "atom l \<sharp> (v,t,i,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,t,i,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,t,i,s,k,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (v,t,i,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,t,i,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,t,i,s,k,sm',sn,sn')" "atom sm' \<sharp> (v,t,i,s,k,sn,sn')"
          "atom sn \<sharp> (v,t,i,s,k,sn')" "atom sn' \<sharp> (v,t,i,s,k)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqStTermP.simps [of l _ _ v i sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair t t))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = t], simp)
    apply (rule Ex_I [where x = t], auto intro: HPair_cong Mem_Eats_I2)
    apply (blast intro: Disj_I1 Disj_I2 VarP_neq_IndP)
    done
qed

corollary SubstTermP_Ind: "{VarP v, IndP w, TermP t} \<turnstile> SubstTermP v t w w"
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,w,t,k)" "atom k \<sharp> (v,w,t)"
    by (metis obtain_fresh)
  thus ?thesis 
    by (force simp: SubstTermP.simps [of s _ _ _ _ k]
              intro: SeqStTermP_Ind [THEN cut2])
qed
 
subsection \<open>Non-atomic cases\<close>

lemma SeqStTermP_Eats:
  assumes sk: "atom s \<sharp> (k,s1,s2,k1,k2,t1,t2,u1,u2,v,i)"
              "atom k \<sharp> (t1,t2,u1,u2,v,i)"
    shows "{SeqStTermP v i t1 u1 s1 k1, SeqStTermP v i t2 u2 s2 k2} 
           \<turnstile> Ex s (Ex k (SeqStTermP v i (Q_Eats t1 t2) (Q_Eats u1 u2) (Var s) (Var k)))" (*<*)
proof -
  obtain km::name and kn::name and j::name and k'::name and l::name and sl::name and sl'::name  
     and m::name and n::name and sm::name and sm'::name and sn::name and sn'::name
    where atoms2: "atom km \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,kn,j,k',l,sl,sl',m,n,sm,sm',sn,sn')"
         "atom kn \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,j,k',l,sl,sl',m,n,sm,sm',sn,sn')"
         "atom j  \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,k',l,sl,sl',m,n,sm,sm',sn,sn')"
      and atoms: "atom k' \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,l,sl,sl',m,n,sm,sm',sn,sn')"
         "atom l  \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sl',m,n,sm,sm',sn,sn')" 
         "atom sl'\<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,m,n,sm,sm',sn,sn')"
         "atom m  \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,n,sm,sm',sn,sn')" 
         "atom n  \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sm,sm',sn,sn')"
         "atom sm \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sm',sn,sn')" 
         "atom sm'\<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sn,sn')"
         "atom sn \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i,sn')" 
         "atom sn'\<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,v,i)"
    by (metis obtain_fresh) 
  let ?hyp = "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s), SeqStTermP v i t1 u1 s1 k1, SeqStTermP v i t2 u2 s2 k2}"
  show ?thesis
     using sk atoms
     apply (auto simp: SeqStTermP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I SeqStTermP_imp_OrdP thin1 thin2)
     apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2)))"])
     apply (simp_all (no_asm_simp))
     apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"], simp)
     apply (rule Conj_I [OF _ Conj_I])
     apply (metis SeqStTermP_imp_VarP thin1)
     apply (blast intro: LstSeqP_SeqAppendP_Eats SeqStTermP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sl (Ex sl'
              (HPair (SUCC (SUCC (Var k'))) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
               ((Var sl EQ v AND Var sl' EQ i OR (IndP (Var sl) OR Var sl NEQ v) AND Var sl' EQ Var sl) OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn'
                 (Var m IN SUCC (SUCC (Var k')) AND
                  Var n IN SUCC (SUCC (Var k')) AND
                  HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
                  HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
                  Var sl EQ Q_Eats (Var sm) (Var sn) AND Var sl' EQ Q_Eats (Var sm') (Var sn'))))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Q_Eats t1 t2"])
       using sk atoms apply simp
       apply (rule Ex_I [where x="Q_Eats u1 u2"], simp)
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x="SUCC (Var k')"], simp)
       apply (rule Ex_I [where x=t1], simp)
       apply (rule Ex_I [where x=u1], simp)
       apply (rule Ex_I [where x=t2], simp)
       apply (rule Ex_I [where x=u2], simp)
       apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I LstSeqP_OrdP Mem_SUCC_I1)
       apply (rule Conj_I [OF Mem_SUCC_Refl Conj_I])
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem1 [THEN cut3] Mem_SUCC_Refl SeqStTermP_imp_LstSeqP [THEN cut1] 
                           LstSeqP_imp_Mem)
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] Mem_SUCC_Refl SeqStTermP_imp_LstSeqP [THEN cut1] 
                           HaddP_SUCC1 [THEN cut1] LstSeqP_imp_Mem)
       done
     next
       show "?hyp \<turnstile> All2 l (SUCC (SUCC (Var k')))
                (Ex sl (Ex sl'
                  (HPair (Var l) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
                   ((Var sl EQ v AND Var sl' EQ i OR (IndP (Var sl) OR Var sl NEQ v) AND Var sl' EQ Var sl) OR
                    Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn'
                       (Var m IN Var l AND
                        Var n IN Var l AND
                        HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
                        HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Eats t1 t2) (Q_Eats u1 u2))) AND
                        Var sl EQ Q_Eats (Var sm) (Var sn) AND Var sl' EQ Q_Eats (Var sm') (Var sn')))))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
     apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
     apply (rule All_I Imp_I)+
     apply (rule HaddP_Mem_cases [where i=j])
     using sk atoms atoms2 apply simp_all
     apply (rule AssumeH)
     apply (blast intro: OrdP_SUCC_I LstSeqP_OrdP)
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: SeqStTermP.simps [of l s1 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule Conj_I)
     apply (metis Mem_Eats_I1 SeqAppendP_Mem1 rotate3 thin2 thin4)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all)
     apply (rule Conj_I, rule AssumeH)+
     apply (blast del: Disj_EH intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     \<comment> \<open>... the sequence buildup via s2\<close>
     apply (simp add: SeqStTermP.simps [of l s2 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule cut_same [where A="OrdP (Var j)"])
     apply (metis HaddP_imp_OrdP rotate2 thin2)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply simp_all
     apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
     apply (blast intro!: Ord_IN_Ord, simp)
     apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var n"]])
     apply (blast intro!: Ord_IN_Ord, simp)
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var km"], simp)
     apply (rule Ex_I [where x="Var kn"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all)
     apply (rule Conj_I [OF _ Conj_I])
     apply (blast intro!: HaddP_Mem_cancel_left [THEN Iff_MP2_same] OrdP_SUCC_I intro: LstSeqP_OrdP Hyp)+
     apply (blast intro: OrdP_Trans Hyp Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] HaddP_imp_OrdP [THEN cut1])
     done
   qed
qed (*>*)

theorem SubstTermP_Eats:
   "{SubstTermP v i t1 u1, SubstTermP v i t2 u2} \<turnstile> SubstTermP v i (Q_Eats t1 t2) (Q_Eats u1 u2)"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,t1,u1,t2,u2)" "atom k1 \<sharp> (v,i,t1,u1,t2,u2,s1)"  
          "atom s2 \<sharp> (v,i,t1,u1,t2,u2,k1,s1)" "atom k2 \<sharp> (v,i,t1,u1,t2,u2,s2,k1,s1)"
          "atom s  \<sharp> (v,i,t1,u1,t2,u2,k2,s2,k1,s1)"
          "atom k  \<sharp> (v,i,t1,u1,t2,u2,s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
   thus ?thesis
     by (auto intro!: SeqStTermP_Eats [THEN cut2]
              simp: SubstTermP.simps [of s _ _ _ "(Q_Eats u1 u2)" k] 
                    SubstTermP.simps [of s1 v i t1 u1 k1]  
                    SubstTermP.simps [of s2 v i t2 u2 k2])
qed

subsection \<open>Substitution over a constant\<close>

lemma SeqConstP_lemma:
  assumes "atom m \<sharp> (s,k,c,n,sm,sn)"  "atom n \<sharp> (s,k,c,sm,sn)" 
          "atom sm \<sharp> (s,k,c,sn)"      "atom sn \<sharp> (s,k,c)"
    shows "{ SeqConstP s k c }
           \<turnstile> c EQ Zero OR
             Ex m (Ex n (Ex sm (Ex sn (Var m IN k AND Var n IN k AND
                   SeqConstP s (Var m) (Var sm) AND
                   SeqConstP s (Var n) (Var sn) AND
                   c EQ Q_Eats (Var sm) (Var sn)))))"  (*<*)
proof -
  obtain l::name and sl::name where "atom l \<sharp> (s,k,c,sl,m,n,sm,sn)" "atom sl \<sharp> (s,k,c,m,n,sm,sn)"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqCTermP.simps [of l s k sl m n sm sn])
    apply (rule Conj_EH)+
    apply (rule All2_SUCC_E [THEN rotate2], auto del: Disj_EH)
    apply (rule cut_same [where A = "c EQ (Var sl)"])
    apply (metis Assume AssumeH(4) LstSeqP_EQ)
    apply (rule Disj_EH)
    apply (blast intro: Disj_I1 Sym Trans)
    \<comment> \<open>now the quantified case\<close>
    apply (auto intro!: Disj_I2)
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (simp_all add: SeqCTermP.simps [of l s _ sl m n sm sn])
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    \<comment> \<open>first SeqCTermP subgoal\<close>
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>next SeqCTermP subgoal\<close>
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>finally, the equality pair\<close>
    apply (blast intro: Trans)
    done
qed (*>*)

lemma SeqConstP_imp_SubstTermP: "{SeqConstP s kk c, TermP t} \<turnstile> SubstTermP \<lceil>Var w\<rceil> t c c" (*<*)
proof -
  obtain j::name and k::name and l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom j \<sharp> (s,kk,c,t,k,l,sl,m,n,sm,sn)"  "atom k \<sharp> (s,kk,c,t,l,sl,m,n,sm,sn)" 
                 "atom l \<sharp> (s,kk,c,t,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,kk,c,t,m,n,sm,sn)"
                 "atom m \<sharp> (s,kk,c,t,n,sm,sn)"  "atom n \<sharp> (s,kk,c,t,sm,sn)" 
                 "atom sm \<sharp> (s,kk,c,t,sn)"      "atom sn \<sharp> (s,kk,c,t)"
    by (metis obtain_fresh)
  have "{ OrdP (Var k), TermP t } \<turnstile> All j (SeqConstP s (Var k) (Var j) IMP SubstTermP \<lceil>Var w\<rceil> t (Var j) (Var j))"
        (is "_ \<turnstile> ?scheme")
    proof (rule OrdIndH [where j=l])
      show "atom l \<sharp> (k, ?scheme)" using atoms
        by simp 
    next
      show "{TermP t} \<turnstile> All k (OrdP (Var k) IMP (All2 l (Var k) (?scheme(k::= Var l)) IMP ?scheme))"
        using atoms apply auto
        apply (rule Swap)
        apply (rule cut_same)
        apply (rule cut1 [OF SeqConstP_lemma [of m s "Var k" "Var j" n sm sn]], auto)
        \<comment> \<open>case 1, @{term Zero}\<close>
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same])
        apply (auto intro: SubstTermP_Zero [THEN cut1])
        \<comment> \<open>case 2, @{term Q_Eats}\<close>
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate2], simp)
        apply (rule SubstTermP_Eats [THEN cut2])
        \<comment> \<open>First argument\<close>
        apply (rule All2_E' [OF Hyp, where x="Var m"], blast+, simp_all)
        apply (force intro: All_E [where x="Var sm"])
        \<comment> \<open>Second argument\<close>
        apply (rule All2_E' [OF Hyp, where x="Var n"], blast+, simp_all)
        apply (rule All_E [where x="Var sn"], auto)
        done
    qed
  hence "{OrdP (Var k), TermP t} \<turnstile> (SeqConstP s (Var k) (Var j) IMP SubstTermP \<lceil>Var w\<rceil> t (Var j) (Var j))(j::=c)"
    by (metis All_D)
  hence "{TermP t} \<turnstile> (SeqConstP s (Var k) c IMP SubstTermP \<lceil>Var w\<rceil> t c c)"
    using atoms by simp (metis Imp_cut SeqCTermP_imp_OrdP)
  hence "{TermP t} \<turnstile> (SeqConstP s (Var k) c IMP SubstTermP \<lceil>Var w\<rceil> t c c)(k::=kk)"
    using atoms by (force intro!: Subst)
  thus ?thesis
    using atoms by (simp add: anti_deduction) 
qed (*>*)

theorem SubstTermP_Const: "{ConstP c, TermP t} \<turnstile> SubstTermP \<lceil>Var w\<rceil> t c c"
proof -
  obtain s::name and k::name where "atom s \<sharp> (c,t,w,k)" "atom k \<sharp> (c,t,w)" 
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: CTermP.simps [of k s c] SeqConstP_imp_SubstTermP)
qed


section \<open>Substitution on Formulas\<close>

subsection \<open>Membership\<close>

lemma SubstAtomicP_Mem: 
  "{SubstTermP v i x x', SubstTermP v i y y'} \<turnstile> SubstAtomicP v i (Q_Mem x y) (Q_Mem x' y')"
proof -
  obtain t::name and u::name and t'::name and u'::name 
    where "atom t \<sharp> (v,i,x,x',y,y',t',u,u')" "atom t' \<sharp> (v,i,x,x',y,y',u,u')"
          "atom u \<sharp> (v,i,x,x',y,y',u')" "atom u' \<sharp> (v,i,x,x',y,y')"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (simp add: SubstAtomicP.simps [of t _ _ _ _ t' u u'])
    apply (rule Ex_I [where x = x], simp)
    apply (rule Ex_I [where x = y], simp)
    apply (rule Ex_I [where x = x'], simp)
    apply (rule Ex_I [where x = y'], auto intro: Disj_I2)
    done
qed

lemma SeqSubstFormP_Mem:
  assumes "atom s \<sharp> (k,x,y,x',y',v,i)" "atom k \<sharp> (x,y,x',y',v,i)"
    shows "{SubstTermP v i x x', SubstTermP v i y y'} 
           \<turnstile> Ex s (Ex k (SeqSubstFormP v i (Q_Mem x y) (Q_Mem x' y') (Var s) (Var k)))"
proof -
  let ?vs = "(s,k,x,y,x',y',v,i)"
  obtain l::name and sl::name and sl'::name and m::name and n::name and sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (?vs,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (?vs,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (?vs,n,sm,sm',sn,sn')" "atom n \<sharp> (?vs,sm,sm',sn,sn')"
          "atom sm \<sharp> (?vs,sm',sn,sn')" "atom sm' \<sharp> (?vs,sn,sn')"
          "atom sn \<sharp> (?vs,sn')" "atom sn' \<sharp> ?vs"
    by (metis obtain_fresh) 
  thus ?thesis
    using assms
    apply (auto simp: SeqSubstFormP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair (Q_Mem x y) (Q_Mem x' y')))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = "Q_Mem x y"], simp)
    apply (rule Ex_I [where x = "Q_Mem x' y'"], auto intro: Mem_Eats_I2 HPair_cong)
    apply (blast intro: SubstAtomicP_Mem [THEN cut2] Disj_I1)
    done
qed

lemma SubstFormP_Mem: 
  "{SubstTermP v i x x', SubstTermP v i y y'} \<turnstile> SubstFormP v i (Q_Mem x y) (Q_Mem x' y')"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,x,y,x',y')" "atom k1 \<sharp> (v,i,x,y,x',y',s1)"  
       "atom s2 \<sharp> (v,i,x,y,x',y',k1,s1)" "atom k2 \<sharp> (v,i,x,y,x',y',s2,k1,s1)"
       "atom s  \<sharp> (v,i,x,y,x',y',k2,s2,k1,s1)" "atom k  \<sharp> (v,i,x,y,x',y',s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SubstFormP.simps [of s v i "(Q_Mem x y)" _ k] 
                   SubstFormP.simps [of s1 v i x x' k1]  
                   SubstFormP.simps [of s2 v i y y' k2]
             intro: SubstTermP_imp_TermP SubstTermP_imp_VarP SeqSubstFormP_Mem thin1)
qed

subsection \<open>Equality\<close>

lemma SubstAtomicP_Eq:
  "{SubstTermP v i x x', SubstTermP v i y y'} \<turnstile> SubstAtomicP v i (Q_Eq x y) (Q_Eq x' y')"
proof -
  obtain t::name and u::name and t'::name  and u'::name 
    where "atom t \<sharp> (v,i,x,x',y,y',t',u,u')" "atom t' \<sharp> (v,i,x,x',y,y',u,u')"
          "atom u \<sharp> (v,i,x,x',y,y',u')" "atom u' \<sharp> (v,i,x,x',y,y')"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (simp add: SubstAtomicP.simps [of t _ _ _ _ t' u u'])
    apply (rule Ex_I [where x = x], simp)
    apply (rule Ex_I [where x = y], simp)
    apply (rule Ex_I [where x = x'], simp)
    apply (rule Ex_I [where x = y'], auto intro: Disj_I1)
    done
qed

lemma SeqSubstFormP_Eq:
  assumes sk: "atom s \<sharp> (k,x,y,x',y',v,i)" "atom k \<sharp> (x,y,x',y',v,i)"
    shows "{SubstTermP v i x x', SubstTermP v i y y'} 
           \<turnstile> Ex s (Ex k (SeqSubstFormP v i (Q_Eq x y) (Q_Eq x' y') (Var s) (Var k)))"
proof -
  let ?vs = "(s,k,x,y,x',y',v,i)"
  obtain l::name and sl::name and sl'::name and m::name and n::name and sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (?vs,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (?vs,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (?vs,n,sm,sm',sn,sn')" "atom n \<sharp> (?vs,sm,sm',sn,sn')"
          "atom sm \<sharp> (?vs,sm',sn,sn')" "atom sm' \<sharp> (?vs,sn,sn')"
          "atom sn \<sharp> (?vs,sn')" "atom sn' \<sharp> ?vs"
    by (metis obtain_fresh) 
  thus ?thesis
    using sk
    apply (auto simp: SeqSubstFormP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
    apply (rule Ex_I [where x = "Eats Zero (HPair Zero (HPair (Q_Eq x y) (Q_Eq x' y')))"], simp)
    apply (rule Ex_I [where x = Zero], auto intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = "Q_Eq x y"], simp)
    apply (rule Ex_I [where x = "Q_Eq x' y'"], auto)
    apply (metis Mem_Eats_I2 Assume HPair_cong Refl)
    apply (blast intro: SubstAtomicP_Eq [THEN cut2] Disj_I1)
    done
qed

lemma SubstFormP_Eq: 
  "{SubstTermP v i x x', SubstTermP v i y y'} \<turnstile> SubstFormP v i (Q_Eq x y) (Q_Eq x' y')"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,x,y,x',y')" "atom k1 \<sharp> (v,i,x,y,x',y',s1)"  
          "atom s2 \<sharp> (v,i,x,y,x',y',k1,s1)" "atom k2 \<sharp> (v,i,x,y,x',y',s2,k1,s1)"
          "atom s  \<sharp> (v,i,x,y,x',y',k2,s2,k1,s1)" "atom k  \<sharp> (v,i,x,y,x',y',s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SubstFormP.simps [of s v i "(Q_Eq x y)" _ k] 
                   SubstFormP.simps [of s1 v i x x' k1]  
                   SubstFormP.simps [of s2 v i y y' k2] 
             intro: SeqSubstFormP_Eq SubstTermP_imp_TermP SubstTermP_imp_VarP thin1)
qed

subsection \<open>Negation\<close>

lemma SeqSubstFormP_Neg:
  assumes "atom s \<sharp> (k,s1,k1,x,x',v,i)" "atom k \<sharp> (s1,k1,x,x',v,i)"
    shows "{SeqSubstFormP v i x x' s1 k1, TermP i, VarP v} 
           \<turnstile> Ex s (Ex k (SeqSubstFormP v i (Q_Neg x) (Q_Neg x') (Var s) (Var k)))" (*<*)
proof -
  let ?vs = "(s1,k1,s,k,x,x',v,i)"
  obtain l::name and sl::name and sl'::name and m::name and n::name and 
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (?vs,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (?vs,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (?vs,n,sm,sm',sn,sn')" "atom n \<sharp> (?vs,sm,sm',sn,sn')"
         "atom sm \<sharp> (?vs,sm',sn,sn')" "atom sm' \<sharp> (?vs,sn,sn')"
         "atom sn \<sharp> (?vs,sn')" "atom sn' \<sharp> ?vs"
    by (metis obtain_fresh) 
  let ?hyp = "{RestrictedP s1 (SUCC k1) (Var s), OrdP k1, SeqSubstFormP v i x x' s1 k1, TermP i, VarP v}"
  show ?thesis
     using assms atoms
     apply (auto simp: SeqSubstFormP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule cut_same [where A="OrdP k1"])
     apply (metis SeqSubstFormP_imp_OrdP thin2)
     apply (rule cut_same [OF exists_RestrictedP [of s s1 "SUCC k1"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x')))"])
     apply (simp_all (no_asm_simp))
     apply (rule Ex_I [where x="(SUCC k1)"])
     apply (simp add: flip_fresh_fresh)
     apply (rule Conj_I)
     apply (blast intro: RestrictedP_LstSeqP_Eats [THEN cut2] SeqSubstFormP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sl (Ex sl'
              (HPair (SUCC k1) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
               (SubstAtomicP v i (Var sl) (Var sl') OR
                Ex m (Ex n
                   (Ex sm (Ex sm'
                       (Ex sn (Ex sn'
                       (Var m IN SUCC k1 AND
                        Var n IN SUCC k1 AND
                        HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
                        HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
                        (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                          Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm')))))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Q_Neg x"])
       using assms atoms apply simp
       apply (rule Ex_I [where x="Q_Neg x'"], simp)
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x=x], simp)
       apply (rule_tac x=x' in Ex_I, simp)
       apply (rule Ex_I [where x=x], simp)
       apply (rule_tac x=x' in Ex_I, simp)
       apply (rule Conj_I [OF Mem_SUCC_Refl])+
       apply (blast intro: Disj_I1 Disj_I2 Mem_Eats_I1 RestrictedP_Mem [THEN cut3] Mem_SUCC_Refl 
                     SeqSubstFormP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem)
       done
     next
       show "?hyp \<turnstile> All2 l (SUCC k1)
                (Ex sl (Ex sl'
                    (HPair (Var l) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
                     (SubstAtomicP v i (Var sl) (Var sl') OR
                      Ex m (Ex n
                         (Ex sm (Ex sm'
                             (Ex sn (Ex sn'
                                 (Var m IN Var l AND
                                  Var n IN Var l AND
                                  HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
                                  HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Neg x) (Q_Neg x'))) AND
                                  (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                            Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm'))))))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule All_I Imp_I)+
     using assms atoms apply simp_all
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: SeqSubstFormP.simps [of l s1 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2], auto del: Disj_EH)
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], auto del: Disj_EH)
     apply (blast intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] OrdP_Trans [OF OrdP_SUCC_I])+
     done
   qed
qed (*>*)

theorem SubstFormP_Neg: "{SubstFormP v i x x'} \<turnstile> SubstFormP v i (Q_Neg x) (Q_Neg x')"
proof -
  obtain k1::name and s1::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,x,x')"        "atom k1 \<sharp> (v,i,x,x',s1)"  
          "atom s  \<sharp> (v,i,x,x',k1,s1)"  "atom k  \<sharp> (v,i,x,x',s,k1,s1)" 
     by (metis obtain_fresh)
   thus ?thesis
     by (force simp: SubstFormP.simps [of s v i "Q_Neg x" _ k] SubstFormP.simps [of s1 v i x x' k1] 
               intro: SeqSubstFormP_Neg [THEN cut3])
qed

subsection \<open>Disjunction\<close>

lemma SeqSubstFormP_Disj:
  assumes "atom s \<sharp> (k,s1,s2,k1,k2,x,y,x',y',v,i)" "atom k \<sharp> (s1,s2,k1,k2,x,y,x',y',v,i)"
    shows "{SeqSubstFormP v i x x' s1 k1, 
            SeqSubstFormP v i y y' s2 k2, TermP i, VarP v} 
           \<turnstile> Ex s (Ex k (SeqSubstFormP v i (Q_Disj x y) (Q_Disj x' y') (Var s) (Var k)))" (*<*)
proof -
  let ?vs = "(s1,s2,s,k1,k2,k,x,y,x',y',v,i)"
  obtain km::name and kn::name and j::name and k'::name 
     and l::name and sl::name and sl'::name and m::name and n::name  
     and sm::name and sm'::name and sn::name and sn'::name
    where atoms2: "atom km \<sharp> (kn,j,k',l,s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom kn \<sharp> (j,k',l,s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom j \<sharp> (k',l,s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl,sl',m,n,sm,sm',sn,sn')"
     and atoms: "atom k' \<sharp> (l,s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl,sl',m,n,sm,sm',sn,sn')" 
         "atom l \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sl',m,n,sm,sm',sn,sn')" 
         "atom sl' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,n,sm,sm',sn,sn')" 
         "atom n \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sm,sm',sn,sn')"
         "atom sm \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sm',sn,sn')" 
         "atom sm' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sn,sn')"
         "atom sn \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i,sn')" 
         "atom sn' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',v,i)"
    by (metis obtain_fresh) 
  let ?hyp = "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s),
               SeqSubstFormP v i x x' s1 k1, SeqSubstFormP v i y y' s2 k2, TermP i, VarP v}"
  show ?thesis
     using assms atoms
     apply (auto simp: SeqSubstFormP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I SeqSubstFormP_imp_OrdP thin1 thin2)
     apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC(SUCC(Var k'))) (HPair(Q_Disj x y)(Q_Disj x' y')))"])
     apply (simp_all (no_asm_simp))
     apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"], simp)
     apply (rule Conj_I)
     apply (blast intro: LstSeqP_SeqAppendP_Eats SeqSubstFormP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sl (Ex sl'
                 (HPair (SUCC (SUCC (Var k'))) (HPair (Var sl) (Var sl')) IN
                  Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
                  (SubstAtomicP v i (Var sl) (Var sl') OR
                   Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn'
                      (Var m IN SUCC (SUCC (Var k')) AND
                       Var n IN SUCC (SUCC (Var k')) AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
                       (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                          Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm')))))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Q_Disj x y"])
       using assms atoms apply simp
       apply (rule Ex_I [where x="Q_Disj x' y'"], simp)
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x="SUCC (Var k')"], simp)
       apply (rule Ex_I [where x=x], simp)
       apply (rule_tac x=x' in Ex_I, simp)
       apply (rule Ex_I [where x=y], simp)
       apply (rule_tac x=y' in Ex_I, simp)
       apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I LstSeqP_OrdP Mem_SUCC_I1)
       apply (rule Conj_I [OF Mem_SUCC_Refl])
       apply (blast intro: Disj_I1 Mem_Eats_I1 Mem_SUCC_Refl SeqSubstFormP_imp_LstSeqP [THEN cut1] 
           LstSeqP_imp_Mem SeqAppendP_Mem1 [THEN cut3] SeqAppendP_Mem2 [THEN cut4] HaddP_SUCC1 [THEN cut1])
       done
     next
       show "?hyp \<turnstile>  All2 l (SUCC (SUCC (Var k')))
     (Ex sl
       (Ex sl'
         (HPair (Var l) (HPair (Var sl) (Var sl')) IN
          Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
          (SubstAtomicP v i (Var sl) (Var sl') OR
           Ex m (Ex n
              (Ex sm (Ex sm'
                  (Ex sn (Ex sn'
                      (Var m IN Var l AND
                       Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Q_Disj x y) (Q_Disj x' y'))) AND
                       (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                            Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm'))))))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
     apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
     apply (rule All_I Imp_I)+
     apply (rule HaddP_Mem_cases [where i=j])
     using assms atoms atoms2 apply simp_all
     apply (rule AssumeH)
     apply (blast intro: OrdP_SUCC_I LstSeqP_OrdP)
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: SeqSubstFormP.simps [of l s1 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule Conj_I [OF Mem_Eats_I1])
     apply (metis SeqAppendP_Mem1 rotate3 thin2 thin4)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all (no_asm_simp))
     apply (rule Conj_I, rule AssumeH)+
     apply (rule Conj_I)
     apply (blast intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     apply (blast intro: Disj_I1 Disj_I2 OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     \<comment> \<open>... the sequence buildup via s2\<close>
     apply (simp add: SeqSubstFormP.simps [of l s2 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule cut_same [where A="OrdP (Var j)"])
     apply (metis HaddP_imp_OrdP rotate2 thin2)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
     apply (blast intro: Ord_IN_Ord, simp)
     apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var n"]])
     apply (metis AssumeH(6) Ord_IN_Ord0 rotate8, simp)
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var km"], simp)
     apply (rule Ex_I [where x="Var kn"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all (no_asm_simp))
     apply (rule Conj_I [OF _ Conj_I])
     apply (blast intro!: HaddP_Mem_cancel_left [THEN Iff_MP2_same] OrdP_SUCC_I intro: LstSeqP_OrdP Hyp)+
     apply (blast del: Disj_EH  intro: OrdP_Trans Hyp 
                  intro!: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] HaddP_imp_OrdP [THEN cut1])
     done
   qed
qed (*>*)

theorem SubstFormP_Disj: 
  "{SubstFormP v i x x', SubstFormP v i y y'} \<turnstile> SubstFormP v i (Q_Disj x y) (Q_Disj x' y')"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,x,y,x',y')"        "atom k1 \<sharp> (v,i,x,y,x',y',s1)"  
          "atom s2 \<sharp> (v,i,x,y,x',y',k1,s1)"  "atom k2 \<sharp> (v,i,x,y,x',y',s2,k1,s1)"
          "atom s  \<sharp> (v,i,x,y,x',y',k2,s2,k1,s1)" "atom k  \<sharp> (v,i,x,y,x',y',s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
   thus ?thesis
     by (force simp: SubstFormP.simps [of s v i "Q_Disj x y" _ k] 
                     SubstFormP.simps [of s1 v i x x' k1]  
                     SubstFormP.simps [of s2 v i y y' k2]
               intro: SeqSubstFormP_Disj [THEN cut4])
qed

subsection \<open>Existential\<close>

lemma SeqSubstFormP_Ex:
  assumes "atom s \<sharp> (k,s1,k1,x,x',v,i)" "atom k \<sharp> (s1,k1,x,x',v,i)"
    shows "{SeqSubstFormP v i x x' s1 k1, TermP i, VarP v} 
           \<turnstile> Ex s (Ex k (SeqSubstFormP v i (Q_Ex x) (Q_Ex x') (Var s) (Var k)))" (*<*)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name
     and sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s1,k1,s,k,x,x',v,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s1,k1,s,k,x,x',v,i,sl',m,n,sm,sm',sn,sn')" 
         "atom sl' \<sharp> (s1,k1,s,k,x,x',v,i,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s1,k1,s,k,x,x',v,i,n,sm,sm',sn,sn')" 
         "atom n \<sharp> (s1,k1,s,k,x,x',v,i,sm,sm',sn,sn')"
         "atom sm \<sharp> (s1,k1,s,k,x,x',v,i,sm',sn,sn')" 
         "atom sm' \<sharp> (s1,k1,s,k,x,x',v,i,sn,sn')"
         "atom sn \<sharp> (s1,k1,s,k,x,x',v,i,sn')" 
         "atom sn' \<sharp> (s1,k1,s,k,x,x',v,i)"
    by (metis obtain_fresh) 
  let ?hyp = "{RestrictedP s1 (SUCC k1) (Var s), OrdP k1, SeqSubstFormP v i x x' s1 k1, TermP i, VarP v}"
  show ?thesis
     using assms atoms
     apply (auto simp: SeqSubstFormP.simps [of l "Var s" _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule cut_same [where A="OrdP k1"])
     apply (metis SeqSubstFormP_imp_OrdP thin2)
     apply (rule cut_same [OF exists_RestrictedP [of s s1 "SUCC k1"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x')))"], simp)
     apply (rule Ex_I [where x="(SUCC k1)"], simp)
     apply (rule Conj_I)
     apply (blast intro: RestrictedP_LstSeqP_Eats [THEN cut2] SeqSubstFormP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sl (Ex sl'
          (HPair (SUCC k1) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
           (SubstAtomicP v i (Var sl) (Var sl') OR
            Ex m (Ex n
               (Ex sm (Ex sm'
                   (Ex sn (Ex sn'
                       (Var m IN SUCC k1 AND
                        Var n IN SUCC k1 AND
                        HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
                        HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
                        (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                          Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm')))))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Q_Ex x"])
       using assms atoms apply simp
       apply (rule Ex_I [where x="Q_Ex x'"], simp)
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x=x], simp)
       apply (rule_tac x=x' in Ex_I, simp)
       apply (rule Ex_I [where x=x], simp)
       apply (rule_tac x=x' in Ex_I, simp)
       apply (rule Conj_I [OF Mem_SUCC_Refl])+
       apply (blast intro: Disj_I2 Mem_Eats_I1 RestrictedP_Mem [THEN cut3] Mem_SUCC_Refl 
                      SeqSubstFormP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem)
       done
     next
       show "?hyp 
             \<turnstile> All2 l (SUCC k1)
                (Ex sl (Ex sl'
                    (HPair (Var l) (HPair (Var sl) (Var sl')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
                     (SubstAtomicP v i (Var sl) (Var sl') OR
                      Ex m (Ex n
                         (Ex sm (Ex sm'
                             (Ex sn (Ex sn'
                                 (Var m IN Var l AND
                                  Var n IN Var l AND
                                  HPair (Var m) (HPair (Var sm) (Var sm')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
                                  HPair (Var n) (HPair (Var sn) (Var sn')) IN Eats (Var s) (HPair (SUCC k1) (HPair (Q_Ex x) (Q_Ex x'))) AND
                                  (Var sl EQ Q_Disj (Var sm) (Var sn) AND Var sl' EQ Q_Disj (Var sm') (Var sn') OR
                            Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm') OR Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm'))))))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     using assms atoms 
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (auto simp add: SeqSubstFormP.simps [of l s1 _ _ _ sl sl' m n sm sm' sn sn'])
     apply (rule Swap)
     apply (rule All2_E, auto del: Disj_EH)
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"])
     apply (auto intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] OrdP_Trans [OF OrdP_SUCC_I] del: Disj_EH)
     done
   qed
qed (*>*)

theorem SubstFormP_Ex: "{SubstFormP v i x x'} \<turnstile> SubstFormP v i (Q_Ex x) (Q_Ex x')"
proof -
  obtain k1::name and s1::name and k::name and s::name
    where "atom s1 \<sharp> (v,i,x,x')"        "atom k1 \<sharp> (v,i,x,x',s1)"  
          "atom s  \<sharp> (v,i,x,x',k1,s1)"  "atom k  \<sharp> (v,i,x,x',s,k1,s1)" 
     by (metis obtain_fresh)
   thus ?thesis
     by (force simp: SubstFormP.simps [of s v i "Q_Ex x" _ k] SubstFormP.simps [of s1 v i x x' k1] 
               intro: SeqSubstFormP_Ex [THEN cut3])
qed


section \<open>Constant Terms\<close>

lemma ConstP_Zero: "{} \<turnstile> ConstP Zero"
  by (auto intro: Sigma_fm_imp_thm [OF CTermP_sf] simp: Const_0 ground_fm_aux_def supp_conv_fresh)

lemma SeqConstP_Eats:
  assumes "atom s \<sharp> (k,s1,s2,k1,k2,t1,t2)" "atom k \<sharp> (s1,s2,k1,k2,t1,t2)"
    shows "{SeqConstP s1 k1 t1, SeqConstP s2 k2 t2}
           \<turnstile> Ex s (Ex k (SeqConstP (Var s) (Var k) (Q_Eats t1 t2)))" (*<*)
proof -
  obtain km::name and kn::name and j::name and k'::name 
     and l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms:
         "atom km \<sharp> (kn,j,k',l,s1,s2,s,k1,k2,k,t1,t2,sl,m,n,sm,sn)"
         "atom kn \<sharp> (j,k',l,s1,s2,s,k1,k2,k,t1,t2,sl,m,n,sm,sn)"
         "atom j \<sharp> (k',l,s1,s2,s,k1,k2,k,t1,t2,sl,m,n,sm,sn)" 
         "atom k' \<sharp> (l,s1,s2,s,k1,k2,k,t1,t2,sl,m,n,sm,sn)"
         "atom l \<sharp> (s1,s2,s,k1,k2,k,t1,t2,sl,m,n,sm,sn)" 
         "atom sl \<sharp> (s1,s2,s,k1,k2,k,t1,t2,m,n,sm,sn)"
         "atom m \<sharp> (s1,s2,s,k1,k2,k,t1,t2,n,sm,sn)" 
         "atom n \<sharp> (s1,s2,s,k1,k2,k,t1,t2,sm,sn)"
         "atom sm \<sharp> (s1,s2,s,k1,k2,k,t1,t2,sn)" 
         "atom sn \<sharp> (s1,s2,s,k1,k2,k,t1,t2)"
    by (metis obtain_fresh) 
  let ?hyp = "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s), 
              SeqConstP s1 k1 t1, SeqConstP s2 k2 t2}"
  show ?thesis
     using assms atoms
     apply (auto simp: SeqCTermP.simps [of l "Var s" _ sl m n sm sn])
     apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I SeqCTermP_imp_OrdP thin1 thin2)
     apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2))"], simp)
     apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"], simp)
     apply (rule Conj_I)
     apply (blast intro: LstSeqP_SeqAppendP_Eats SeqCTermP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sl (HPair (SUCC (SUCC (Var k'))) (Var sl) IN Eats (Var s) 
                          (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2))   AND
                (Var sl EQ Zero OR Fls OR
                 Ex m (Ex n(Ex sm (Ex sn
                      (Var m IN SUCC (SUCC (Var k')) AND
                       Var n IN SUCC (SUCC (Var k')) AND
                       HPair (Var m) (Var sm) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2)) AND
                       HPair (Var n) (Var sn) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2)) AND
                       Var sl EQ Q_Eats (Var sm) (Var sn)))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Q_Eats t1 t2"])
       using assms atoms apply simp
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)+
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x="SUCC (Var k')"], simp)
       apply (rule Ex_I [where x=t1], simp)
       apply (rule Ex_I [where x=t2], simp)
       apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I LstSeqP_OrdP Mem_SUCC_I1)
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem1 [THEN cut3] SeqAppendP_Mem2 [THEN cut4]
                 Mem_SUCC_Refl SeqCTermP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem HaddP_SUCC1 [THEN cut1])
       done
     next
       show "?hyp \<turnstile> All2 l (SUCC (SUCC (Var k')))
                 (Ex sl
                   (HPair (Var l) (Var sl) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2)) AND
                    (Var sl EQ Zero OR Fls OR
                     Ex m (Ex n (Ex sm (Ex sn
                          (Var m IN Var l AND
                           Var n IN Var l AND
                           HPair (Var m) (Var sm) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2)) AND
                           HPair (Var n) (Var sn) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (Q_Eats t1 t2)) AND
                           Var sl EQ Q_Eats (Var sm) (Var sn))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
     apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
     apply (rule All_I Imp_I)+
     apply (rule HaddP_Mem_cases [where i=j])
     using assms atoms apply simp_all
     apply (rule AssumeH)
     apply (blast intro: OrdP_SUCC_I LstSeqP_OrdP)
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: SeqCTermP.simps [of l s1 _ sl m n sm sn])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2], auto del: Disj_EH)
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Conj_I)
     apply (rule Mem_Eats_I1)
     apply (metis SeqAppendP_Mem1 rotate3 thin2 thin4)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply simp_all
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Conj_I, rule AssumeH)+
     apply (blast del: Disj_EH intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     \<comment> \<open>... the sequence buildup via s2\<close>
     apply (simp add: SeqCTermP.simps [of l s2 _ sl m n sm sn])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2], auto del: Disj_EH)
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule cut_same [where A="OrdP (Var j)"])
     apply (metis HaddP_imp_OrdP rotate2 thin2)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
     apply (blast intro: Ord_IN_Ord, simp)
     apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var n"]])
     apply (metis AssumeH(6) Ord_IN_Ord0 rotate8, simp)
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var km"], simp)
     apply (rule Ex_I [where x="Var kn"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sn"], simp_all)
     apply (rule Conj_I [OF _ Conj_I])
     apply (blast intro!: HaddP_Mem_cancel_left [THEN Iff_MP2_same] OrdP_SUCC_I intro: LstSeqP_OrdP Hyp)+
     apply (blast del: Disj_EH  intro: OrdP_Trans Hyp 
                  intro!: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] HaddP_imp_OrdP [THEN cut1])
     done
   qed
qed (*>*)

theorem ConstP_Eats: "{ConstP t1, ConstP t2} \<turnstile> ConstP (Q_Eats t1 t2)"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (t1,t2)" "atom k1 \<sharp> (t1,t2,s1)"  
          "atom s2 \<sharp> (t1,t2,k1,s1)" "atom k2 \<sharp> (t1,t2,s2,k1,s1)"
          "atom s  \<sharp> (t1,t2,k2,s2,k1,s1)" "atom k  \<sharp> (t1,t2,s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
   thus ?thesis
     by (auto simp: CTermP.simps [of k s "(Q_Eats t1 t2)"] 
                    CTermP.simps [of k1 s1 t1]  CTermP.simps [of k2 s2 t2]
              intro!:  SeqConstP_Eats [THEN cut2])
qed


section \<open>Proofs\<close>

lemma PrfP_inference:
  assumes "atom s \<sharp> (k,s1,s2,k1,k2,\<alpha>1,\<alpha>2,\<beta>)" "atom k \<sharp> (s1,s2,k1,k2,\<alpha>1,\<alpha>2,\<beta>)"
    shows "{PrfP s1 k1 \<alpha>1, PrfP s2 k2 \<alpha>2, ModPonP \<alpha>1 \<alpha>2 \<beta> OR ExistsP \<alpha>1 \<beta> OR SubstP \<alpha>1 \<beta>} 
           \<turnstile> Ex k (Ex s (PrfP (Var s) (Var k) \<beta>))" (*<*)
proof -
  obtain km::name and kn::name and j::name and k'::name 
     and l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms:
         "atom km \<sharp> (kn,j,k',l,s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sl,m,n,sm,sn)"
         "atom kn \<sharp> (j,k',l,s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sl,m,n,sm,sn)"
         "atom j \<sharp> (k',l,s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sl,m,n,sm,sn)"
         "atom k' \<sharp> (l,s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sl,m,n,sm,sn)" 
         "atom l \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sl,m,n,sm,sn)"
         "atom sl \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,m,n,sm,sn)" 
         "atom m \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,n,sm,sn)" 
         "atom n \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sm,sn)" 
         "atom sm \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>,sn)" 
         "atom sn \<sharp> (s1,s2,s,k1,k2,k,\<alpha>1,\<alpha>2,\<beta>)"
    by (metis obtain_fresh) 
  let ?hyp = "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s), 
              PrfP s1 k1 \<alpha>1, PrfP s2 k2 \<alpha>2, ModPonP \<alpha>1 \<alpha>2 \<beta> OR ExistsP \<alpha>1 \<beta> OR SubstP \<alpha>1 \<beta>}"
  show ?thesis
     using assms atoms
     apply (simp add: PrfP.simps [of l "Var s" sl m n sm sn])
     apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I PrfP_imp_OrdP thin1 thin2)
     apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"], simp)
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>)"], simp)
     apply (rule Conj_I)
     apply (blast intro: LstSeqP_SeqAppendP_Eats PrfP_imp_LstSeqP [THEN cut1])
     proof (rule All2_SUCC_I, simp_all)
       show "?hyp \<turnstile> Ex sn
                 (HPair (SUCC (SUCC (Var k'))) (Var sn) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                  (AxiomP (Var sn) OR
                   Ex m (Ex l (Ex sm (Ex sl
                      (Var m IN SUCC (SUCC (Var k')) AND
                       Var l IN SUCC (SUCC (Var k')) AND
                       HPair (Var m) (Var sm) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                       HPair (Var l) (Var sl) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                       (ModPonP (Var sm) (Var sl) (Var sn) OR ExistsP (Var sm) (Var sn) OR SubstP (Var sm) (Var sn))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="\<beta>"])
       using assms atoms apply simp
       apply (rule Conj_I, metis Mem_Eats_I2 Refl)
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x="SUCC (Var k')"], simp)
       apply (rule_tac x=\<alpha>1 in Ex_I, simp)
       apply (rule_tac x=\<alpha>2 in Ex_I, simp)
       apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I LstSeqP_OrdP Mem_SUCC_I1)
       apply (rule Conj_I [OF Mem_SUCC_Refl Conj_I])
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem1 [THEN cut3] Mem_SUCC_Refl PrfP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem)
       apply (blast del: Disj_EH  intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] Mem_SUCC_Refl 
                     PrfP_imp_LstSeqP [THEN cut1] HaddP_SUCC1 [THEN cut1] LstSeqP_imp_Mem)
       done
     next
       show "?hyp \<turnstile> All2 n (SUCC (SUCC (Var k')))
               (Ex sn
                 (HPair (Var n) (Var sn) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                  (AxiomP (Var sn) OR
                   Ex m (Ex l (Ex sm (Ex sl
                      (Var m IN Var n AND
                       Var l IN Var n AND
                       HPair (Var m) (Var sm) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                       HPair (Var l) (Var sl) IN Eats (Var s) (HPair (SUCC (SUCC (Var k'))) \<beta>) AND
                       (ModPonP (Var sm) (Var sl) (Var sn) OR ExistsP (Var sm) (Var sn) OR SubstP (Var sm) (Var sn)))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
     apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
     apply (rule All_I Imp_I)+
     apply (rule HaddP_Mem_cases [where i=j])
     using assms atoms apply simp_all
     apply (rule AssumeH)
     apply (blast intro: OrdP_SUCC_I LstSeqP_OrdP)
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: PrfP.simps [of l s1 sl m n sm sn])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Conj_I)
     apply (rule Mem_Eats_I1)
     apply (metis SeqAppendP_Mem1 rotate3 thin2 thin4)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var l"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sl"], simp_all)
     apply (rule Conj_I, rule AssumeH)+
     apply (blast del: Disj_EH intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     \<comment> \<open>... the sequence buildup via s2\<close>
     apply (simp add: PrfP.simps [of l s2 sl m n sm sn])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule cut_same [where A="OrdP (Var j)"])
     apply (metis HaddP_imp_OrdP rotate2 thin2)
     apply (rule Conj_I)
     apply (blast intro!: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
     apply (blast intro: Ord_IN_Ord, simp)
     apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var l"]])
     apply (blast intro!: Ord_IN_Ord)
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var km"], simp)
     apply (rule Ex_I [where x="Var kn"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sl"], simp_all)
     apply (rule Conj_I [OF _ Conj_I])
     apply (blast intro!: HaddP_Mem_cancel_left [THEN Iff_MP2_same] OrdP_SUCC_I intro: LstSeqP_OrdP Hyp)+
     apply (blast del: Disj_EH  intro: OrdP_Trans Hyp 
                  intro!: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] HaddP_imp_OrdP [THEN cut1])
     done
   qed
qed (*>*)

corollary PfP_inference: "{PfP \<alpha>1, PfP \<alpha>2, ModPonP \<alpha>1 \<alpha>2 \<beta> OR ExistsP \<alpha>1 \<beta> OR SubstP \<alpha>1 \<beta>} \<turnstile> PfP \<beta>"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (\<alpha>1,\<alpha>2,\<beta>)" "atom k1 \<sharp> (\<alpha>1,\<alpha>2,\<beta>,s1)"  
          "atom s2 \<sharp> (\<alpha>1,\<alpha>2,\<beta>,k1,s1)""atom k2 \<sharp> (\<alpha>1,\<alpha>2,\<beta>,s2,k1,s1)"
          "atom s  \<sharp> (\<alpha>1,\<alpha>2,\<beta>,k2,s2,k1,s1)"
          "atom k  \<sharp> (\<alpha>1,\<alpha>2,\<beta>,s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
   thus ?thesis
     apply (simp add: PfP.simps [of k s \<beta>] PfP.simps [of k1 s1 \<alpha>1]  PfP.simps [of k2 s2 \<alpha>2])
     apply (auto intro!: PrfP_inference [of s k "Var s1" "Var s2", THEN cut3] del: Disj_EH)
     done
qed

theorem PfP_implies_SubstForm_PfP: 
   assumes "H \<turnstile> PfP y" "H \<turnstile> SubstFormP x t y z"
     shows "H \<turnstile> PfP z"
proof -
  obtain u::name and v::name
    where atoms: "atom u \<sharp> (t,x,y,z,v)"   "atom v \<sharp> (t,x,y,z)"
    by (metis obtain_fresh) 
  show ?thesis
    apply (rule PfP_inference [of y, THEN cut3])
    apply (rule assms)+
    using atoms
    apply (auto simp: SubstP.simps [of u _ _ v] intro!: Disj_I2)
    apply (rule Ex_I [where x=x], simp)
    apply (rule Ex_I [where x=t], simp add: assms)
    done
qed

theorem PfP_implies_ModPon_PfP: "\<lbrakk>H \<turnstile> PfP (Q_Imp x y); H \<turnstile> PfP x\<rbrakk> \<Longrightarrow> H \<turnstile> PfP y" 
  by (force intro: PfP_inference [of x, THEN cut3] Disj_I1  simp add: ModPonP_def)

corollary PfP_implies_ModPon_PfP_quot: "\<lbrakk>H \<turnstile> PfP \<lceil>\<alpha> IMP \<beta>\<rceil>; H \<turnstile> PfP \<lceil>\<alpha>\<rceil>\<rbrakk> \<Longrightarrow> H \<turnstile> PfP \<lceil>\<beta>\<rceil>" 
  by (auto simp: quot_fm_def intro: PfP_implies_ModPon_PfP)

end

