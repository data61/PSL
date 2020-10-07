chapter\<open>Uniqueness Results: Syntactic Relations are Functions\<close>

theory Functions
imports Coding_Predicates
begin

subsection \<open>SeqStTermP\<close>

lemma not_IndP_VarP: "{IndP x, VarP x} \<turnstile> A"
proof -
  obtain m::name  where "atom m \<sharp> (x,A)"
    by (metis obtain_fresh) 
  thus ?thesis
    by  (auto simp: fresh_Pair) (blast intro: ExFalso cut_same [OF VarP_cong [THEN Iff_MP_same]])
qed

text\<open>It IS a pair, but not just any pair.\<close>
lemma IndP_HPairE: "insert (IndP (HPair (HPair Zero (HPair Zero Zero)) x)) H \<turnstile> A"
proof -
  obtain m::name  where "atom m \<sharp> (x,A)"
    by (metis obtain_fresh)
  hence "{ IndP (HPair (HPair Zero (HPair Zero Zero)) x) } \<turnstile> A"
    by (auto simp: IndP.simps [of m] HTuple_minus_1 intro: thin1)
  thus ?thesis
    by (metis Assume cut1)
qed

lemma atom_HPairE: 
  assumes "H \<turnstile> x EQ HPair (HPair Zero (HPair Zero Zero)) y"
    shows "insert (IndP x OR x NEQ v) H \<turnstile> A"
proof -
  have "{ IndP x OR x NEQ v, x EQ HPair (HPair Zero (HPair Zero Zero)) y } \<turnstile> A"
    by (auto intro!: OrdNotEqP_OrdP_E IndP_HPairE
             intro: cut_same [OF IndP_cong [THEN Iff_MP_same]] 
                    cut_same [OF OrdP_cong [THEN Iff_MP_same]])
  thus ?thesis
    by (metis Assume assms rcut2)
qed

lemma SeqStTermP_lemma:
  assumes "atom m \<sharp> (v,i,t,u,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,i,t,u,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,i,t,u,s,k,sm',sn,sn')" "atom sm' \<sharp> (v,i,t,u,s,k,sn,sn')"
          "atom sn \<sharp> (v,i,t,u,s,k,sn')" "atom sn' \<sharp> (v,i,t,u,s,k)"
    shows "{ SeqStTermP v i t u s k }
           \<turnstile> ((t EQ v AND u EQ i) OR
              ((IndP t OR t NEQ v) AND u EQ t)) OR
              Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN k AND Var n IN k AND
                       SeqStTermP v i (Var sm) (Var sm') s (Var m) AND
                       SeqStTermP v i (Var sn) (Var sn') s (Var n) AND
                       t EQ Q_Eats (Var sm) (Var sn) AND
                       u EQ Q_Eats (Var sm') (Var sn')))))))"
proof -
  obtain l::name and sl::name and sl'::name
    where "atom l \<sharp> (v,i,t,u,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,i,t,u,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,i,t,u,s,k,m,n,sm,sm',sn,sn')"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqStTermP.simps [of l s k v i sl sl' m n sm sm' sn sn'])
    apply (rule Conj_EH Ex_EH All2_SUCC_E [THEN rotate2] | simp)+
    apply (rule cut_same [where A = "HPair t u EQ HPair (Var sl) (Var sl')"])
    apply (metis Assume AssumeH(4) LstSeqP_EQ)
    apply clarify
    apply (rule Disj_EH)
    apply (rule Disj_I1)
    apply (rule anti_deduction)
    apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same])
    apply (rule Sym_L [THEN rotate2])
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], force)
    \<comment> \<open>now the quantified case\<close>
    \<comment> \<open>auto could be used but is VERY SLOW\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Disj_I2)
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sm'"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (rule Ex_I [where x = "Var sn'"], simp)
    apply (simp_all add: SeqStTermP.simps [of l s _ v i sl sl' m n sm sm' sn sn'])
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    \<comment> \<open>first SeqStTermP subgoal\<close>
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>next SeqStTermP subgoal\<close>
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>finally, the equality pair\<close>
    apply (blast intro: Trans)
    done
qed


lemma SeqStTermP_unique: "{SeqStTermP v a t u s kk, SeqStTermP v a t u' s' kk'} \<turnstile> u' EQ u"
proof -
  obtain i::name and j::name and j'::name and k::name and k'::name and l::name
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
     and m2::name and n2::name and sm2::name and sn2::name and sm2'::name and sn2'::name
    where atoms:  "atom i \<sharp> (s,s',v,a,t,u,u')"   "atom j \<sharp> (s,s',v,a,t,i,t,u,u')"
                  "atom j' \<sharp> (s,s',v,a,t,i,j,t,u,u')"
                  "atom k \<sharp> (s,s',v,a,t,u,u',kk',i,j,j')" "atom k' \<sharp> (s,s',v,a,t,u,u',k,i,j,j')"
                  "atom l \<sharp> (s,s',v,a,t,i,j,j',k,k')"
                  "atom m \<sharp> (s,s',v,a,i,j,j',k,k',l)"   "atom n \<sharp> (s,s',v,a,i,j,j',k,k',l,m)"
                  "atom sm \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n)"  "atom sn \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm)"
                  "atom sm' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn)"   "atom sn' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm')"
                  "atom m2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn')"   "atom n2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2)"
                  "atom sm2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2)"  "atom sn2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2)"
                  "atom sm2' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2)"   "atom sn2' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2,sm2')"
    by (metis obtain_fresh)
  have "{ OrdP (Var k), VarP v }
       \<turnstile> All i (All j (All j' (All k' (SeqStTermP v a (Var i) (Var j) s (Var k)
                                  IMP (SeqStTermP v a (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))"
    apply (rule OrdIndH [where j=l])
    using atoms apply auto
    apply (rule Swap)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqStTermP_lemma [of m v a "Var i" "Var j" s "Var k" n sm sm' sn sn']], simp_all, blast)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqStTermP_lemma [of m2 v a "Var i" "Var j'" s' "Var k'" n2 sm2 sm2' sn2 sn2']], simp_all, blast)
    apply (rule Disj_EH Conj_EH)+
    \<comment> \<open>case 1, both sides equal "v"\<close>
    apply (blast intro: Trans Sym)
    \<comment> \<open>case 2, @{term "Var i EQ v"} and also @{term "IndP (Var i) OR Var i NEQ v"}\<close>
    apply (rule Conj_EH Disj_EH)+
    apply (blast intro: IndP_cong [THEN Iff_MP_same] not_IndP_VarP [THEN cut2])
    apply (metis Assume OrdNotEqP_E)
    \<comment> \<open>case 3, both a variable and a pair\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule cut_same [where A = "VarP (Q_Eats (Var sm) (Var sn))"])
    apply (blast intro: Trans Sym VarP_cong [where x=v, THEN Iff_MP_same] Hyp, blast)
    \<comment> \<open>towards remaining cases\<close>
    apply (rule Disj_EH Ex_EH)+
    \<comment> \<open>case 4, @{term "Var i EQ v"} and also @{term "IndP (Var i) OR Var i NEQ v"}\<close>
    apply (blast intro: IndP_cong [THEN Iff_MP_same] not_IndP_VarP [THEN cut2] OrdNotEqP_E)
    \<comment> \<open>case 5, @{term "Var i EQ v"} for both\<close>
    apply (blast intro: Trans Sym)
    \<comment> \<open>case 6, both an atom and a pair\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all 
    apply (rule atom_HPairE)
    apply (simp add: HTuple.simps)
    apply (blast intro: Trans)
    \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH Ex_EH)+
    apply simp_all
    \<comment> \<open>case 7, both an atom and a pair\<close>
    apply (rule cut_same [where A = "VarP (Q_Eats (Var sm2) (Var sn2))"])
    apply (blast intro: Trans Sym VarP_cong [where x=v, THEN Iff_MP_same] Hyp, blast)
    \<comment> \<open>case 8, both an atom and a pair\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule atom_HPairE)
    apply (simp add: HTuple.simps)
    apply (blast intro: Trans)
    \<comment> \<open>case 9, two Eats terms\<close>
    apply (rule Ex_EH Disj_EH Conj_EH)+
    apply simp_all
    apply (rule All_E' [OF Hyp, where x="Var m"], blast)
    apply (rule All_E' [OF Hyp, where x="Var n"], blast, simp)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule All_E [where x="Var sn", THEN rotate2], simp)
    apply (rule All_E [where x="Var sn'"], simp)
    apply (rule All_E [where x="Var sn2'"], simp)
    apply (rule All_E [where x="Var n2"], simp)
    apply (rule cut_same [where A = "Q_Eats (Var sm) (Var sn) EQ Q_Eats (Var sm2) (Var sn2)"])
    apply (blast intro: Sym Trans, clarify)
    apply (rule cut_same [where A = "SeqStTermP v a (Var sn) (Var sn2') s' (Var n2)"])
    apply (blast intro: Hyp SeqStTermP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule cut_same [where A = "SeqStTermP v a (Var sm) (Var sm2') s' (Var m2)"])
    apply (blast intro: Hyp SeqStTermP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (blast intro: HPair_cong Trans [OF Hyp Sym])
    done
  hence p1: "{OrdP (Var k), VarP v}
             \<turnstile> (All j (All j' (All k' (SeqStTermP v a (Var i) (Var j) s (Var k)
                 IMP (SeqStTermP v a (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))(i::=t)"
    by (metis All_D)
  have p2: "{OrdP (Var k), VarP v}
         \<turnstile> (All j' (All k' (SeqStTermP v a t (Var j) s (Var k)
                 IMP (SeqStTermP v a t (Var j') s' (Var k') IMP Var j' EQ Var j))))(j::=u)"
    apply (rule All_D)
    using atoms p1 by simp
  have p3: "{OrdP (Var k), VarP v}
             \<turnstile> (All k' (SeqStTermP v a t u s (Var k) IMP (SeqStTermP v a t (Var j') s' (Var k') IMP Var j' EQ u)))(j'::=u')"
    apply (rule All_D)
    using atoms p2 by simp
  have p4: "{OrdP (Var k), VarP v}
          \<turnstile> (SeqStTermP v a t u s (Var k) IMP (SeqStTermP v a t u' s' (Var k') IMP u' EQ u))(k'::=kk')"
    apply (rule All_D)
    using atoms p3 by simp
  hence "{SeqStTermP v a t u s (Var k), VarP v} \<turnstile> SeqStTermP v a t u s (Var k) IMP (SeqStTermP v a t u' s' kk' IMP u' EQ u)"
    using atoms apply simp
    by (metis SeqStTermP_imp_OrdP rcut1)
  hence "{VarP v} \<turnstile> ((SeqStTermP v a t u s (Var k) IMP (SeqStTermP v a t u' s' kk' IMP u' EQ u)))"
    by (metis Assume MP_same Imp_I)
  hence "{VarP v} \<turnstile> ((SeqStTermP v a t u s (Var k) IMP (SeqStTermP v a t u' s' kk' IMP u' EQ u)))(k::=kk)"
   using atoms by (force intro!: Subst)
  hence "{VarP v} \<turnstile> SeqStTermP v a t u s kk IMP (SeqStTermP v a t u' s' kk' IMP u' EQ u)"
    using atoms by simp
  hence "{SeqStTermP v a t u s kk} \<turnstile> SeqStTermP v a t u s kk IMP (SeqStTermP v a t u' s' kk' IMP u' EQ u)"
    by (metis SeqStTermP_imp_VarP rcut1)
  thus ?thesis
    by (metis Assume AssumeH(2) MP_same rcut1)
qed


theorem SubstTermP_unique: "{SubstTermP v tm t u, SubstTermP v tm t u'} \<turnstile> u' EQ u"
proof -
  obtain s::name and s'::name and k::name and k'::name
    where "atom s \<sharp> (v,tm,t,u,u',k,k')" "atom s' \<sharp> (v,tm,t,u,u',k,k',s)"
          "atom k \<sharp> (v,tm,t,u,u')" "atom k' \<sharp> (v,tm,t,u,u',k)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SubstTermP.simps [of s v tm t u k]  SubstTermP.simps [of s' v tm t u' k'])
       (metis SeqStTermP_unique rotate3 thin1)
qed

subsection\<open>@{term SubstAtomicP}\<close>

lemma SubstTermP_eq:
  "\<lbrakk>H \<turnstile> SubstTermP v tm x z; insert (SubstTermP v tm y z) H \<turnstile> A\<rbrakk> \<Longrightarrow> insert (x EQ y) H \<turnstile> A"
  by (metis Assume rotate2 Iff_E1 cut_same thin1 SubstTermP_cong [OF Refl Refl _ Refl])

lemma SubstAtomicP_unique: "{SubstAtomicP v tm x y, SubstAtomicP v tm x y'} \<turnstile> y' EQ y"
proof -
  obtain t::name and ts::name and u::name and us::name
     and t'::name and ts'::name and u'::name and us'::name
    where "atom t \<sharp> (v,tm,x,y,y',ts,u,us)"  "atom ts \<sharp> (v,tm,x,y,y',u,us)"
          "atom u \<sharp> (v,tm,x,y,y',us)"       "atom us \<sharp> (v,tm,x,y,y')"
          "atom t' \<sharp> (v,tm,x,y,y',t,ts,u,us,ts',u',us')" "atom ts' \<sharp> (v,tm,x,y,y',t,ts,u,us,u',us')"
          "atom u' \<sharp> (v,tm,x,y,y',t,ts,u,us,us')"        "atom us' \<sharp> (v,tm,x,y,y',t,ts,u,us)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (simp add: SubstAtomicP.simps [of t v tm x y ts u us]
                     SubstAtomicP.simps [of t' v tm x y' ts' u' us'])
    apply (rule Ex_EH Disj_EH Conj_EH)+
    apply simp_all
    apply (rule Eq_Trans_E [OF Hyp], auto simp: HTS)
    apply (rule SubstTermP_eq [THEN thin1], blast)
    apply (rule SubstTermP_eq [THEN rotate2], blast)
    apply (rule Trans [OF Hyp Sym], blast)
    apply (rule Trans [OF Hyp], blast)
    apply (metis Assume AssumeH(8) HPair_cong Refl cut2 [OF SubstTermP_unique] thin1)
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
    apply (rule Eq_Trans_E [OF Hyp], auto simp: HTS)
    apply (rule SubstTermP_eq [THEN thin1], blast)
    apply (rule SubstTermP_eq [THEN rotate2], blast)
    apply (rule Trans [OF Hyp Sym], blast)
    apply (rule Trans [OF Hyp], blast)
    apply (metis Assume AssumeH(8) HPair_cong Refl cut2 [OF SubstTermP_unique] thin1)
    done
qed

subsection\<open>@{term SeqSubstFormP}\<close>

lemma SeqSubstFormP_lemma:
  assumes "atom m \<sharp> (v,u,x,y,s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (v,u,x,y,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (v,u,x,y,s,k,sm',sn,sn')"  "atom sm' \<sharp> (v,u,x,y,s,k,sn,sn')"
          "atom sn \<sharp> (v,u,x,y,s,k,sn')"         "atom sn' \<sharp> (v,u,x,y,s,k)"
  shows "{ SeqSubstFormP v u x y s k }
         \<turnstile> SubstAtomicP v u x y  OR
           Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN k AND Var n IN k AND
                       SeqSubstFormP v u (Var sm) (Var sm') s (Var m) AND
                       SeqSubstFormP v u (Var sn) (Var sn') s (Var n) AND
                       (((x EQ Q_Disj (Var sm) (Var sn) AND y EQ Q_Disj (Var sm') (Var sn')) OR
                        (x EQ Q_Neg (Var sm) AND y EQ Q_Neg (Var sm')) OR
                        (x EQ Q_Ex (Var sm) AND y EQ Q_Ex (Var sm'))))))))))"
proof -
  obtain l::name and sl::name and sl'::name
    where "atom l \<sharp> (v,u,x,y,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (v,u,x,y,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (v,u,x,y,s,k,m,n,sm,sm',sn,sn')"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqSubstFormP.simps [of l s k v u sl sl' m n sm sm' sn sn'])
    apply (rule Conj_EH Ex_EH All2_SUCC_E [THEN rotate2] | simp)+
    apply (rule cut_same [where A = "HPair x y EQ HPair (Var sl) (Var sl')"])
    apply (metis Assume AssumeH(4) LstSeqP_EQ)
    apply clarify
    apply (rule Disj_EH)
    apply (blast intro: Disj_I1 SubstAtomicP_cong [THEN Iff_MP2_same])
    \<comment> \<open>now the quantified cases\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Disj_I2)
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sm'"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (rule Ex_I [where x = "Var sn'"], simp)
    apply (simp_all add: SeqSubstFormP.simps [of l s _ v u sl sl' m n sm sm' sn sn'])
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    \<comment> \<open>first SeqSubstFormP subgoal\<close>
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>next SeqSubstFormP subgoal\<close>
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>finally, the equality pairs\<close>
    apply (rule anti_deduction [THEN thin1])
    apply (rule Sym_L [THEN rotate4])
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same])
    apply (rule Sym_L [THEN rotate5])
    apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], force)
    done
qed

lemma 
  shows Neg_SubstAtomicP_Fls:  "{y EQ Q_Neg z,  SubstAtomicP v tm y y'} \<turnstile> Fls"    (is ?thesis1)
    and Disj_SubstAtomicP_Fls: "{y EQ Q_Disj z w, SubstAtomicP v tm y y'} \<turnstile> Fls"  (is ?thesis2)
    and Ex_SubstAtomicP_Fls:   "{y EQ Q_Ex z,   SubstAtomicP v tm y y'} \<turnstile> Fls"    (is ?thesis3)
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (z,w,v,tm,y,y',t',u,u')" "atom t' \<sharp> (z,w,v,tm,y,y',u,u')"
          "atom u \<sharp> (z,w,v,tm,y,y',u')" "atom u' \<sharp> (z,w,v,tm,y,y')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thesis3
    by (auto simp: SubstAtomicP.simps [of t v tm y y' t' u u'] HTS  intro: Eq_Trans_E [OF Hyp])
qed

lemma SeqSubstFormP_eq:
  "\<lbrakk>H \<turnstile> SeqSubstFormP v tm x z s k; insert (SeqSubstFormP v tm y z s k) H \<turnstile> A\<rbrakk> 
   \<Longrightarrow> insert (x EQ y) H \<turnstile> A"
  apply (rule cut_same [OF SeqSubstFormP_cong [OF Assume Refl Refl Refl, THEN Iff_MP_same]])
  apply (auto simp: insert_commute intro: thin1)
  done

lemma SeqSubstFormP_unique: "{SeqSubstFormP v a x y s kk, SeqSubstFormP v a x y' s' kk'} \<turnstile> y' EQ y"
proof -
  obtain i::name and j::name and j'::name and k::name and k'::name and l::name
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
     and m2::name and n2::name and sm2::name and sn2::name and sm2'::name and sn2'::name
    where atoms:  "atom i \<sharp> (s,s',v,a,x,y,y')"   "atom j \<sharp> (s,s',v,a,x,i,x,y,y')"
                  "atom j' \<sharp> (s,s',v,a,x,i,j,x,y,y')"
                  "atom k \<sharp> (s,s',v,a,x,y,y',kk',i,j,j')" "atom k' \<sharp> (s,s',v,a,x,y,y',k,i,j,j')"
                  "atom l \<sharp> (s,s',v,a,x,i,j,j',k,k')"
                  "atom m \<sharp> (s,s',v,a,i,j,j',k,k',l)"   "atom n \<sharp> (s,s',v,a,i,j,j',k,k',l,m)"
                  "atom sm \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n)"  "atom sn \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm)"
                  "atom sm' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn)"   "atom sn' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm')"
                  "atom m2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn')"   "atom n2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2)"
                  "atom sm2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2)"  "atom sn2 \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2)"
                  "atom sm2' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2)"   "atom sn2' \<sharp> (s,s',v,a,i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2,sm2')"
    by (metis obtain_fresh)
  have "{ OrdP (Var k) }
       \<turnstile> All i (All j (All j' (All k' (SeqSubstFormP v a (Var i) (Var j) s (Var k)
                                  IMP (SeqSubstFormP v a (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))"
    apply (rule OrdIndH [where j=l])
    using atoms apply auto
    apply (rule Swap)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqSubstFormP_lemma [of m v a "Var i" "Var j" s "Var k" n sm sm' sn sn']], simp_all, blast)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqSubstFormP_lemma [of m2 v a "Var i" "Var j'" s' "Var k'" n2 sm2 sm2' sn2 sn2']], simp_all, blast)
    apply (rule Disj_EH Conj_EH)+
    \<comment> \<open>case 1, both sides are atomic\<close>
    apply (blast intro: cut2 [OF SubstAtomicP_unique])
    \<comment> \<open>case 2, atomic and also not\<close>
    apply (rule Ex_EH Conj_EH Disj_EH)+
    apply simp_all
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Disj_SubstAtomicP_Fls])
    apply (rule Conj_EH Disj_EH)+
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Neg_SubstAtomicP_Fls])
    apply (rule Conj_EH)+
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Ex_SubstAtomicP_Fls])
    \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH Ex_EH)+
    apply simp_all
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Disj_SubstAtomicP_Fls])
    apply (rule Conj_EH Disj_EH)+
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Neg_SubstAtomicP_Fls])
    apply (rule Conj_EH)+
    apply (metis Assume AssumeH(7) Disj_I1 Neg_I anti_deduction cut2 [OF Ex_SubstAtomicP_Fls])
    \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH Ex_EH)+
    apply simp_all
    \<comment> \<open>case two Disj terms\<close>
    apply (rule All_E' [OF Hyp, where x="Var m"], blast)
    apply (rule All_E' [OF Hyp, where x="Var n"], blast, simp)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule All_E [where x="Var sn", THEN rotate2], simp)
    apply (rule All_E [where x="Var sn'"], simp)
    apply (rule All_E [where x="Var sn2'"], simp)
    apply (rule All_E [where x="Var n2"], simp)
    apply (rule rotate3)
    apply (rule Eq_Trans_E [OF Hyp], blast)
    apply (clarsimp simp add: HTS)
    apply (rule thin1)
    apply (rule Disj_EH [OF ContraProve], blast intro: thin1 SeqSubstFormP_eq)+
    apply (blast intro: HPair_cong Trans [OF Hyp Sym])
    \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH)+
    \<comment> \<open>Negation = Disjunction?\<close>
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
   \<comment> \<open>Existential = Disjunction?\<close>
    apply (rule Conj_EH)
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
     \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH Ex_EH)+
    apply simp_all
    \<comment> \<open>Disjunction = Negation?\<close>
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
    apply (rule Conj_EH Disj_EH)+
    \<comment> \<open>case two Neg terms\<close>
    apply (rule Eq_Trans_E [OF Hyp], blast, clarify)
    apply (rule thin1)
    apply (rule All_E' [OF Hyp, where x="Var m"], blast, simp)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule Disj_EH [OF ContraProve], blast intro: SeqSubstFormP_eq Sym_L)+
    apply (blast intro: HPair_cong Sym Trans [OF Hyp])
    \<comment> \<open>Existential = Negation?\<close>
    apply (rule Conj_EH)+
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
     \<comment> \<open>towards remaining cases\<close>
    apply (rule Conj_EH Disj_EH Ex_EH)+
    apply simp_all
    \<comment> \<open>Disjunction = Existential\<close>
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
    apply (rule Conj_EH Disj_EH Ex_EH)+
    \<comment> \<open>Negation = Existential\<close>
    apply (rule Eq_Trans_E [OF Hyp], blast, force simp add: HTS)
   \<comment> \<open>case two Ex terms\<close>
    apply (rule Conj_EH)+
    apply (rule Eq_Trans_E [OF Hyp], blast, clarify)
    apply (rule thin1)
    apply (rule All_E' [OF Hyp, where x="Var m"], blast, simp)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule Disj_EH [OF ContraProve], blast intro: SeqSubstFormP_eq Sym_L)+
    apply (blast intro: HPair_cong Sym Trans [OF Hyp])
    done
  hence p1: "{OrdP (Var k)}
             \<turnstile> (All j (All j' (All k' (SeqSubstFormP v a (Var i) (Var j) s (Var k)
                 IMP (SeqSubstFormP v a (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))(i::=x)"
    by (metis All_D)
  have p2: "{OrdP (Var k)}
            \<turnstile> (All j' (All k' (SeqSubstFormP v a x (Var j) s (Var k)
                 IMP (SeqSubstFormP v a x (Var j') s' (Var k') IMP Var j' EQ Var j))))(j::=y)"
    apply (rule All_D)
    using atoms p1 by simp
  have p3: "{OrdP (Var k)}
            \<turnstile> (All k' (SeqSubstFormP v a x y s (Var k) 
                 IMP (SeqSubstFormP v a x (Var j') s' (Var k') IMP Var j' EQ y)))(j'::=y')"
    apply (rule All_D)
    using atoms p2 by simp
  have p4: "{OrdP (Var k)}
          \<turnstile> (SeqSubstFormP v a x y s (Var k) IMP (SeqSubstFormP v a x y' s' (Var k') IMP y' EQ y))(k'::=kk')"
    apply (rule All_D)
    using atoms p3 by simp
  hence "{OrdP (Var k)} \<turnstile> SeqSubstFormP v a x y s (Var k) IMP (SeqSubstFormP v a x y' s' kk' IMP y' EQ y)"
    using atoms by simp
  hence "{SeqSubstFormP v a x y s (Var k)} 
         \<turnstile> SeqSubstFormP v a x y s (Var k) IMP (SeqSubstFormP v a x y' s' kk' IMP y' EQ y)"
    by (metis SeqSubstFormP_imp_OrdP rcut1)
  hence "{} \<turnstile> SeqSubstFormP v a x y s (Var k) IMP (SeqSubstFormP v a x y' s' kk' IMP y' EQ y)"
    by (metis Assume Disj_Neg_2 Disj_commute anti_deduction Imp_I)
  hence "{} \<turnstile> ((SeqSubstFormP v a x y s (Var k) IMP (SeqSubstFormP v a x y' s' kk' IMP y' EQ y)))(k::=kk)"
    using atoms by (force intro!: Subst)
  thus ?thesis
    using atoms by simp (metis DisjAssoc2 Disj_commute anti_deduction)
qed

subsection\<open>@{term SubstFormP}\<close>

theorem SubstFormP_unique: "{SubstFormP v tm x y, SubstFormP v tm x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name and k::name and k'::name
    where "atom s \<sharp> (v,tm,x,y,y',k,k')" "atom s' \<sharp> (v,tm,x,y,y',k,k',s)"
          "atom k \<sharp> (v,tm,x,y,y')" "atom k' \<sharp> (v,tm,x,y,y',k)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp: SubstFormP.simps [of s v tm x y k]  SubstFormP.simps [of s' v tm x y' k']
                    SeqSubstFormP_unique rotate3 thin1)
qed

end

