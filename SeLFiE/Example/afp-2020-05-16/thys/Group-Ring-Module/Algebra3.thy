(**
                                  author Hidetsune Kobayashi
                                  Department of Mathematics
                                  Nihon University
                                  hikoba@math.cst.nihon-u.ac.jp
                                  May 3, 2004.
                                  April 6, 2007 (revised)

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem (continued) 
   section 5.    products
   section 6.    preliminary lemmas for Zassenhaus
   section 7.    homomorphism
   section 8.    gkernel, kernel of a group homomorphism
   section 9.    image, image of a group homomorphism
   section 10.   incuded homomorphisms
   section 11.   Homomorphism therems
   section 12.   isomorphisms
   section 13.   Zassenhaus
   section 14.   an automorphism group
   section 15.   chain of groups I
   section 16.   existence of reduced chain 
   section 17.   existence of reduced chain and composition series"
   section 18.   chain of groups II
   section 19.   Jordan Hoelder theorem
   **)

theory Algebra3 imports Algebra2 begin


section "Setproducts"
       
definition
  commutators:: "_ \<Rightarrow> 'a set" where
  "commutators G = {z. \<exists> a \<in> carrier G. \<exists>b \<in> carrier G.
                        ((a \<cdot>\<^bsub>G\<^esub> b) \<cdot>\<^bsub>G\<^esub> (\<rho>\<^bsub>G\<^esub> a)) \<cdot>\<^bsub>G\<^esub> (\<rho>\<^bsub>G\<^esub> b) = z}" 

lemma (in Group) contain_commutator:"\<lbrakk>G \<guillemotright> H; (commutators G) \<subseteq> H\<rbrakk> \<Longrightarrow> G \<triangleright> H" 
apply (rule cond_nsg[of "H"], assumption)
apply (rule ballI)+
 apply (frule_tac h = h in sg_subset_elem[of "H"], assumption,
        frule_tac a = h in i_closed,
        frule_tac a = a in i_closed,
        frule_tac a = a and b = h in mult_closed, assumption+,
        frule_tac a = "a \<cdot> h" and b = "\<rho> a" in mult_closed, assumption+)
 apply (frule_tac a = "a \<cdot> h \<cdot> (\<rho> a)" and b = "\<rho> h" and c = h in tassoc,
          assumption+)
 apply (simp add:l_i r_unit)
 apply (rule_tac a = "a \<cdot> h \<cdot> \<rho> a \<cdot> \<rho> h \<cdot> h" and A = H and b = "a \<cdot> h \<cdot> \<rho> a" 
        in eq_elem_in,
        rule_tac x = "a \<cdot> h \<cdot> \<rho> a \<cdot> \<rho> h" and y = h in sg_mult_closed[of "H"],
         assumption,
        rule_tac c = "a \<cdot> h \<cdot> \<rho> a \<cdot> \<rho> h" in subsetD[of "commutators G" "H"],
         assumption,
        thin_tac "commutators G \<subseteq> H",
        simp add:commutators_def, blast)
 apply assumption+
done

definition
  s_top :: "[_ , 'a set, 'a set] \<Rightarrow> 'a set " where
  "s_top G H K = {z. \<exists>x \<in> H. \<exists>y \<in> K. (x \<cdot>\<^bsub>G\<^esub> y = z)}"

abbreviation
  S_TOP :: "[('a, 'm) Group_scheme, 'a set, 'a set] \<Rightarrow> 'a set"
    ("(3_ \<diamondop>\<index> _)" [66,67]66) where
  "H \<diamondop>\<^bsub>G\<^esub> K == s_top G H K" 

lemma (in Group) s_top_induced:"\<lbrakk>G \<guillemotright> L; H \<subseteq> L; K \<subseteq> L\<rbrakk> \<Longrightarrow> 
                                        H \<diamondop>\<^bsub>Gp G L\<^esub> K =  H \<diamondop>\<^bsub>G\<^esub> K"
by (simp add:s_top_def Gp_def) 

lemma (in Group) s_top_l_unit:"G \<guillemotright> K \<Longrightarrow> {\<one>} \<diamondop>\<^bsub>G\<^esub> K = K"
apply (rule equalityI)
 apply (rule subsetI, simp add:s_top_def, erule bexE,
        frule_tac h = y in sg_subset_elem[of "K"], assumption+,
        simp add:l_unit)
 apply (rule subsetI,
        simp add:s_top_def)
 apply (frule_tac h = x in sg_subset_elem, assumption,
        frule_tac a = x in l_unit, blast)
done

lemma (in Group) s_top_r_unit:"G \<guillemotright> K \<Longrightarrow> K \<diamondop>\<^bsub>G\<^esub> {\<one>} = K" 
apply (rule equalityI)
apply (rule subsetI, simp add:s_top_def, erule bexE,
       frule_tac h = xa in sg_subset_elem[of "K"], assumption+,
       simp add:r_unit)
apply (rule subsetI,
       simp add:s_top_def,
       frule_tac h = x in sg_subset_elem[of "K"], assumption+,
       frule_tac a = x in r_unit, blast)
done

lemma (in Group) s_top_sub:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K\<rbrakk> \<Longrightarrow>  H \<diamondop>\<^bsub>G\<^esub> K \<subseteq> carrier G"
apply (rule subsetI) apply (simp add:s_top_def)
apply (erule bexE)+
apply (frule_tac h = xa in sg_subset_elem [of "H"], assumption+,
       frule_tac h = y in sg_subset_elem[of "K"], assumption+,
       frule_tac a = xa and b = y in mult_closed, assumption+, simp)
done

lemma (in Group) sg_inc_set_mult:"\<lbrakk>G \<guillemotright> L; H \<subseteq> L; K \<subseteq> L\<rbrakk> \<Longrightarrow> H \<diamondop>\<^bsub>G\<^esub> K \<subseteq> L"
apply (rule subsetI)
apply (simp add:s_top_def, (erule bexE)+)
apply (frule_tac c = xa in subsetD [of "H" "L"], assumption+,
       frule_tac c = y in subsetD [of "K" "L"], assumption+,
       frule_tac x = xa and y = y in sg_mult_closed[of "L"], assumption+)
apply simp
done

lemma (in Group) s_top_sub1:"\<lbrakk>H \<subseteq> (carrier G); K \<subseteq> (carrier G)\<rbrakk> \<Longrightarrow>  
                               H \<diamondop>\<^bsub>G\<^esub> K \<subseteq> carrier G"
apply (rule subsetI)
apply (simp add:s_top_def)
apply (erule bexE)+
apply (frule_tac c = xa in subsetD[of "H" "carrier G"], assumption+,
       frule_tac c = y in subsetD[of "K" "carrier G"], assumption+,
       frule_tac a = xa and b = y in mult_closed, assumption+, simp)
done

lemma (in Group) s_top_elem:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; a \<in> H; b \<in> K\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H \<diamondop>\<^bsub>G\<^esub> K"
by (simp add:s_top_def, blast)

lemma (in Group) s_top_elem1:"\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; a \<in> H; b \<in> K\<rbrakk> \<Longrightarrow>
                    a \<cdot> b \<in> H \<diamondop>\<^bsub>G\<^esub> K "
by (simp add:s_top_def, blast)

lemma (in Group) mem_s_top:"\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; u \<in> H \<diamondop>\<^bsub>G\<^esub> K\<rbrakk> \<Longrightarrow>
                 \<exists>a \<in> H. \<exists>b \<in> K. (a \<cdot> b = u)"
by (simp add:s_top_def)

lemma (in Group) s_top_mono:"\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; H1 \<subseteq> H; K1 \<subseteq> K\<rbrakk>
       \<Longrightarrow>  H1 \<diamondop>\<^bsub>G\<^esub> K1 \<subseteq> H \<diamondop>\<^bsub>G\<^esub> K"
by (rule subsetI, simp add:s_top_def, blast)

lemma (in Group) s_top_unit_closed:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K\<rbrakk> \<Longrightarrow>  \<one> \<in> H \<diamondop>\<^bsub>G\<^esub> K"
apply (frule sg_unit_closed [of "H"], 
       frule sg_unit_closed [of "K"])
apply (cut_tac unit_closed,
       frule l_unit[of "\<one>"])
apply (simp add:s_top_def, blast)
done

lemma (in Group) s_top_commute:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; K \<diamondop>\<^bsub>G\<^esub> H = H \<diamondop>\<^bsub>G\<^esub> K;
       u \<in> H \<diamondop>\<^bsub>G\<^esub> K;  v \<in>  H \<diamondop>\<^bsub>G\<^esub> K\<rbrakk> \<Longrightarrow>  u \<cdot> v \<in> H \<diamondop>\<^bsub>G\<^esub> K"
apply (frule sg_subset[of "H"], frule sg_subset[of "K"],
       frule mem_s_top[of "H" "K" "u"], assumption+, (erule bexE)+,
       frule mem_s_top[of "H" "K" "v"], assumption+, (erule bexE)+)
apply (rotate_tac 4, frule sym, thin_tac "a \<cdot> b = u", frule sym, 
       thin_tac "aa \<cdot> ba = v", simp,
       thin_tac "u = a \<cdot> b", thin_tac "v = aa \<cdot> ba")
apply (frule_tac h = a in sg_subset_elem[of "H"], assumption+,
       frule_tac h = aa in sg_subset_elem[of "H"], assumption+,
       frule_tac h = b in sg_subset_elem[of "K"], assumption+,
       frule_tac h = ba in sg_subset_elem[of "K"], assumption+)
apply (simp add:tOp_assocTr41[THEN sym], simp add:tOp_assocTr42)
apply (frule_tac a = b and b = aa in s_top_elem1[of "K" "H"], assumption+,
       simp, thin_tac "K \<diamondop>\<^bsub>G\<^esub> H = H \<diamondop>\<^bsub>G\<^esub> K")
apply (frule_tac u = "b \<cdot> aa" in mem_s_top[of "H" "K"], assumption+,
       (erule bexE)+, frule sym, thin_tac "ab \<cdot> bb = b \<cdot> aa", simp,
        thin_tac "b \<cdot> aa = ab \<cdot> bb")
apply (frule_tac h = ab in sg_subset_elem[of "H"], assumption+,
       frule_tac h = bb in sg_subset_elem[of "K"], assumption+)
apply (simp add:tOp_assocTr42[THEN sym], simp add:tOp_assocTr41)
apply (frule_tac x = a and y = ab in sg_mult_closed[of "H"], assumption+,
       frule_tac x = bb and y = ba in sg_mult_closed[of "K"], assumption+,
       simp add:s_top_elem1)
done

lemma (in Group) s_top_commute1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; K \<diamondop>\<^bsub>G\<^esub> H = H \<diamondop>\<^bsub>G\<^esub> K;
                                        u \<in> H \<diamondop>\<^bsub>G\<^esub> K\<rbrakk> \<Longrightarrow> (\<rho> u) \<in> H \<diamondop>\<^bsub>G\<^esub> K"
apply (frule sg_subset[of "H"], frule sg_subset[of "K"],
       frule mem_s_top[of "H" "K" "u"], assumption+, (erule bexE)+)
 apply (frule_tac h = a in sg_subset_elem[of "H"], assumption+,
        frule_tac h = b in sg_subset_elem[of "K"], assumption+,
        frule_tac a = a and b = b in i_ab, assumption+,
        rotate_tac 4, frule sym, thin_tac "a \<cdot> b = u", simp,
        thin_tac "\<rho> (a \<cdot> b) = \<rho> b \<cdot> \<rho> a")
 apply (frule_tac x = a in sg_i_closed[of "H"], assumption+,
        frule_tac x = b in sg_i_closed[of "K"], assumption+,
        frule_tac a = "\<rho> b" and b = "\<rho> a" in s_top_elem1[of "K" "H"],
         assumption+, simp)
done

lemma (in Group) s_top_commute_sg:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; K \<diamondop>\<^bsub>G\<^esub> H = H \<diamondop>\<^bsub>G\<^esub> K\<rbrakk> \<Longrightarrow>
                                     G \<guillemotright> (H \<diamondop>\<^bsub>G\<^esub> K)"
apply (subst sg_def)
apply (frule s_top_unit_closed[of "H" "K"], assumption,
       simp add:nonempty, simp add:s_top_sub)
apply ((rule ballI)+, 
       frule_tac u = b in s_top_commute1[of "H" "K"], assumption+,
       rule_tac u = a and v = "\<rho> b" in s_top_commute[of "H" "K"], 
              assumption+)
done

lemma (in Group) s_top_assoc:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; G \<guillemotright> L\<rbrakk> \<Longrightarrow>
                                 (H \<diamondop>\<^bsub>G\<^esub> K) \<diamondop>\<^bsub>G\<^esub> L =  H \<diamondop>\<^bsub>G\<^esub> (K \<diamondop>\<^bsub>G\<^esub> L)"
apply (rule equalityI)
 apply (rule subsetI, simp add:s_top_def) apply (erule exE)
 apply (erule conjE)
 apply (erule bexE)+
 apply (rotate_tac -1, frule sym, thin_tac "xb \<cdot> ya = xa", simp,
        thin_tac "xa = xb \<cdot> ya", frule sym, thin_tac "xb \<cdot> ya \<cdot> y = x",
        simp) 
apply (frule_tac h = xb in sg_subset_elem[of "H"], assumption+,
       frule_tac h = y in sg_subset_elem[of "L"], assumption+,
       frule_tac h = ya in sg_subset_elem[of "K"], assumption+,
       simp add:tassoc, blast)
apply (rule subsetI, simp add:s_top_def,
       erule bexE, erule exE, erule conjE, (erule bexE)+,
       rotate_tac -1, frule sym, thin_tac "xb \<cdot> ya = y", simp,
       thin_tac "y = xb \<cdot> ya")
apply (frule_tac h = xa in sg_subset_elem[of "H"], assumption+,
       frule_tac h = ya in sg_subset_elem[of "L"], assumption+,
       frule_tac h = xb in sg_subset_elem[of "K"], assumption+,
       simp add:tassoc[THEN sym],
       frule sym, thin_tac "xa \<cdot> xb \<cdot> ya = x", simp, blast)
done

lemma (in Group) s_topTr6:"\<lbrakk>G \<guillemotright> H1; G \<guillemotright> H2; G \<guillemotright> K; H1 \<subseteq> K\<rbrakk> \<Longrightarrow>
                               (H1 \<diamondop>\<^bsub>G\<^esub> H2) \<inter> K = H1 \<diamondop>\<^bsub>G\<^esub> (H2 \<inter> K)" 
apply (rule equalityI)
 apply (rule subsetI,
        simp add:s_top_def, erule conjE, (erule bexE)+,
        frule sym, thin_tac "xa \<cdot> y = x", simp,
        frule_tac c = xa in subsetD[of "H1" "K"], assumption+,
        frule_tac x = "xa \<cdot> y" in inEx[of _ "K"], erule bexE,
        frule_tac x = xa in sg_i_closed[of "K"], assumption+,
        frule_tac x = "\<rho> xa" and y = ya in sg_mult_closed[of "K"], 
        assumption+, simp)
 apply (frule_tac h = xa in sg_subset_elem[of "K"], assumption+,
        frule_tac h = "\<rho> xa" in sg_subset_elem[of "K"], assumption+,
        frule_tac h = y in sg_subset_elem[of "H2"], assumption+,
        simp add:tassoc[THEN sym] l_i l_unit)
 apply blast        

 apply (rule subsetI,
        simp add:s_top_def, (erule bexE)+, simp,
        frule sym, thin_tac "xa \<cdot> y = x", simp,
        frule_tac c = xa in subsetD[of "H1" "K"], assumption+,
        frule_tac x = xa and y = y in sg_mult_closed[of "K"], assumption+,
        simp)
 apply blast
done

lemma (in Group) s_topTr6_1:"\<lbrakk>G \<guillemotright> H1; G \<guillemotright> H2; G \<guillemotright> K; H2 \<subseteq> K\<rbrakk> \<Longrightarrow>
                              (H1 \<diamondop>\<^bsub>G\<^esub> H2) \<inter> K = (H1 \<inter> K) \<diamondop>\<^bsub>G\<^esub> H2" 
apply (rule equalityI)
apply (rule subsetI)
apply (simp add:s_top_def, erule conjE, (erule bexE)+)
apply (frule_tac  c = y in subsetD [of "H2" "K"], assumption+)
apply (frule_tac x = y in sg_i_closed [of "K"], assumption)
apply (frule_tac h = xa in sg_subset_elem[of "H1"], assumption+,
       frule_tac h = x in sg_subset_elem[of "K"], assumption+,
       frule_tac h = y in sg_subset_elem[of "K"], assumption+,
       frule_tac h = "\<rho> y" in sg_subset_elem[of "K"], assumption+,
       frule sym, thin_tac "xa \<cdot> y = x", 
       frule_tac x = x and y = "\<rho> y" in sg_mult_closed[of "K"], assumption+,
       simp add:tassoc r_i r_unit, blast)

apply (rule subsetI, simp add:s_top_def, (erule bexE)+,
       simp, erule conjE,
       frule_tac c = y in subsetD[of "H2" "K"], assumption+,
       frule_tac x = xa and y = y in sg_mult_closed[of "K"], assumption+, simp,
       blast)
done

lemma (in Group) l_sub_smult:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K\<rbrakk> \<Longrightarrow> H \<subseteq> H \<diamondop>\<^bsub>G\<^esub> K"
apply (rule subsetI,
       simp add:s_top_def)
apply (frule sg_unit_closed[of "K"],
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       frule_tac a = x in r_unit) 
apply blast
done

lemma (in Group) r_sub_smult:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K\<rbrakk> \<Longrightarrow> K \<subseteq> H \<diamondop>\<^bsub>G\<^esub> K"
apply (rule subsetI,
       simp add:s_top_def)
apply (frule sg_unit_closed[of "H"],
       frule_tac h = x in sg_subset_elem[of "K"], assumption+,
       frule_tac a = x in l_unit)
apply blast
done

lemma (in Group) s_topTr8:"G \<guillemotright> H \<Longrightarrow> H = H \<diamondop>\<^bsub>G\<^esub> H"
apply (frule l_sub_smult[of "H" "H"], assumption)
apply (rule equalityI, assumption)
apply (rule subsetI)
apply (thin_tac "H \<subseteq> H \<diamondop>\<^bsub>G\<^esub> H",
       simp add:s_top_def, (erule bexE)+) 
apply (frule_tac x = xa and y = y in sg_mult_closed[of "H"], assumption+,
       simp)
done

section "Preliminary lemmas for Zassenhaus"

lemma (in Group) Gp_sg_subset:"\<lbrakk>G \<guillemotright> H; Gp G H \<guillemotright> K\<rbrakk> \<Longrightarrow> K \<subseteq> H"
by (frule Group_Gp[of "H"],
       frule Group.sg_subset[of "\<natural>H" "K"], assumption,
       thin_tac "(\<natural>H) \<guillemotright> K", thin_tac "Group (\<natural>H)",
       simp add:Gp_def) 

lemma (in Group) inter_Gp_nsg:"\<lbrakk>G \<triangleright> N; G \<guillemotright> H \<rbrakk> \<Longrightarrow> (\<natural>H) \<triangleright> (H \<inter> N)"
apply (frule Group_Gp[of "H"],
       rule Group.cond_nsg[of "Gp G H" "H \<inter> N"], assumption+,
       frule nsg_sg[of "N"], frule inter_sgs[of "H" "N"], assumption+,
       rule sg_sg [of "H" "H \<inter> N"], assumption+) 
 apply (rule subsetI, simp)
 apply ((rule ballI)+, simp, 
         simp add:Gp_carrier,
         simp add:Gp_mult_induced[of "H"],
         simp add:sg_i_induced[of "H"])
 apply (erule conjE,
        frule_tac x = a in sg_i_closed[of "H"], assumption+,
        frule_tac x = a and y = h in sg_mult_closed, assumption+,
        simp add:Gp_mult_induced[of "H"],
        simp add:sg_mult_closed)
 apply (frule_tac h = a in sg_subset_elem[of "H"], assumption+,
        simp add:nsgPr1_1[of "N"])
done

lemma (in Group) ZassenhausTr0:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1;
       Gp G H \<triangleright> H1; Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> Gp G (H \<inter> K) \<triangleright> (H \<inter> K1)"
apply (frule inter_sgs[of "H" "K"], assumption,
       frule inter_sgs[of "H" "K1"], assumption,
       frule Group_Gp[of "H"],
       frule Group_Gp[of "K"],
       frule Group.nsg_sg[of "\<natural>H" "H1"], assumption+,
       frule Group.nsg_sg[of "\<natural>K" "K1"], assumption+)
apply (rule Group.cond_nsg[of "\<natural>(H \<inter> K)" "H \<inter> K1"],
       simp add:Group_Gp[of "H \<inter> K"])
apply (rule sg_sg[of "H \<inter> K" "H \<inter> K1"], assumption+)
apply (frule Gp_sg_subset[of "K" "K1"], assumption+,
       rule subsetI, simp add:subsetD)
apply ((rule ballI)+, simp) 

apply (frule Gp_sg_subset[of "K" "K1"], assumption+,
       erule conjE, frule_tac c = h in subsetD[of "K1" "K"], assumption+)
apply (rule conjI)
 apply (simp only:Gp_carrier,
        subst Gp_mult_induced1[of "H" "K"], assumption+, simp,
        simp only:sg_i_induced1)
 apply (frule_tac a = a and b = h in Group.mult_closed[of "\<natural>H"],
        simp add:Gp_carrier, simp add:Gp_carrier,
        simp only:Gp_carrier)
 apply (frule_tac a = a in Group.i_closed[of "\<natural>H"],
        simp add:Gp_carrier)
 apply (simp add:Gp_mult_induced1[of "H" "K"], simp add:Gp_carrier,
        subst Gp_mult_induced1[of "H" "K"], assumption+,
        simp add:Gp_mult_induced sg_mult_closed,
        simp add:sg_i_induced sg_i_closed) 
 apply (simp add:Gp_mult_induced sg_i_induced, simp add:sg_mult_closed)

 apply (subst Gp_mult_induced2[of "H" "K"], assumption+,
        simp add:Gp_carrier, simp, subst sg_i_induced2, assumption+,
        simp add:Gp_carrier)
 apply (frule_tac a = a and b = h in Group.mult_closed[of "\<natural>K"],
        simp add:Gp_carrier, simp add:Gp_carrier,
        frule_tac a = a in Group.i_closed[of "\<natural>K"], simp add:Gp_carrier)   
 apply (subst Gp_mult_induced2, assumption+,
        simp add:Gp_carrier, simp add:Gp_mult_induced sg_mult_closed,
        simp add:Gp_carrier, simp add:sg_i_induced sg_i_closed)
apply (rule_tac a = a and h = h in Group.nsgPr1_1[of "\<natural>K" "K1"], assumption+,
       simp add:Gp_carrier, assumption)
done 

lemma (in Group) lcs_sub_s_mult:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; a \<in> H\<rbrakk> \<Longrightarrow> a \<diamondsuit> N \<subseteq> H \<diamondop>\<^bsub>G\<^esub> N"
apply (rule subsetI)
apply (simp add:lcs_def s_top_def, blast)
done

lemma (in Group) rcs_sub_smult:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; a \<in> H\<rbrakk> \<Longrightarrow> N \<bullet> a \<subseteq> N \<diamondop>\<^bsub>G\<^esub> H"
apply (rule subsetI)
 apply (simp add:rcs_def s_top_def, blast)
done

lemma (in Group) smult_commute_sg_nsg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> H \<diamondop>\<^bsub>G\<^esub> N = N \<diamondop>\<^bsub>G\<^esub> H"
apply (frule nsg_sg[of "N"])
apply (rule equalityI)
 apply (rule subsetI,
        simp add:s_top_def, (erule bexE)+,
        frule_tac h = xa in sg_subset_elem, assumption+,
        frule_tac h = y in sg_subset_elem, assumption,
        frule_tac a = xa and b = y in mult_closed, assumption,
        frule_tac a = xa in i_closed,
        frule_tac a = "xa \<cdot> y" and b = "\<rho> xa" and c = xa in tassoc,
        assumption+,
        frule sym, thin_tac "xa \<cdot> y = x", simp,
        thin_tac "x = xa \<cdot> y", simp add:l_i r_unit,
        frule_tac a = xa and h = y in nsgPr1_1[of "N"], assumption+)
 apply blast

 apply (rule subsetI)
 apply (simp add:s_top_def, (erule bexE)+,
        frule_tac h = xa in sg_subset_elem, assumption+,
        frule_tac h = y in sg_subset_elem, assumption,
        frule_tac a = xa and b = y in mult_closed, assumption,
        frule_tac a = y in i_closed,
        frule_tac a = y and b = "\<rho> y" and c = "xa \<cdot> y" in tassoc,
        assumption+,
        frule sym, thin_tac "xa \<cdot> y = x", simp,
        thin_tac "x = xa \<cdot> y", simp add:r_i l_unit,
        frule_tac a = y and h = xa in nsgPr2[of "N"], assumption+,
        frule sym, thin_tac "xa \<cdot> y = y \<cdot> (\<rho> y \<cdot> (xa \<cdot> y))")
 apply blast
done  

lemma (in Group) smult_sg_nsg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> G \<guillemotright> H \<diamondop>\<^bsub>G\<^esub> N"
apply (frule  smult_commute_sg_nsg[of "H" "N"], assumption+,
       frule nsg_sg[of "N"],
       rule s_top_commute_sg[of "H" "N"], assumption+,
       rule sym, assumption)
done
         
lemma (in Group) smult_nsg_sg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> G \<guillemotright> N \<diamondop>\<^bsub>G\<^esub> H"
apply (frule smult_commute_sg_nsg[THEN sym, of "H" "N"], assumption+)
apply (simp add:smult_sg_nsg)
done

lemma (in Group) Gp_smult_sg_nsg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> Group (Gp G (H \<diamondop>\<^bsub>G\<^esub> N))"
apply (frule smult_sg_nsg[of "H" "N"], assumption+)
apply (simp add:Group_Gp)
done  

lemma (in Group) N_sg_HN:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> Gp G (H \<diamondop>\<^bsub>G\<^esub> N) \<guillemotright> N"
apply (frule smult_sg_nsg[of "H" "N"], assumption+,
       frule nsg_sg[of "N"],
       frule r_sub_smult[of "H" "N"], assumption+)
apply (rule sg_sg[of "H \<diamondop>\<^bsub>G\<^esub> N" "N"], assumption+)
done

lemma (in Group) K_absorb_HK:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; H \<subseteq> K\<rbrakk> \<Longrightarrow>  H \<diamondop>\<^bsub>G\<^esub> K = K"
apply (frule r_sub_smult[of "H" "K"], assumption+)
apply (rule equalityI)
apply (thin_tac "K \<subseteq> H \<diamondop>\<^bsub>G\<^esub> K",
       rule subsetI, simp add:s_top_def, (erule bexE)+,
       frule_tac c = xa in subsetD[of "H" "K"], assumption+,
       frule_tac x = xa and y = y in sg_mult_closed[of "K"], assumption+,
       simp)
apply assumption
done
 
lemma (in Group) nsg_Gp_nsg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N; N \<subseteq> H\<rbrakk> \<Longrightarrow> Gp G H \<triangleright> N"
apply (frule Group_Gp[of "H"],
       frule nsg_sg[of "N"], 
       frule sg_sg[of "H" "N"], assumption+,
       rule Group.cond_nsg[of "\<natural>H" "N"], assumption+)
apply ((rule ballI)+,
       frule_tac c = h in subsetD[of "N" "H"], assumption+,
       simp add:Gp_carrier,
       simp add:Gp_mult_induced[of "H"] sg_i_induced[of "H"] 
                sg_mult_closed sg_i_closed)
apply (rule_tac a = a and h = h in nsgPr1_1[of "N"], assumption+,
       rule_tac h = a in sg_subset_elem[of "H"], assumption+)
done

lemma (in Group) Gp_smult_nsg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> Gp G (H \<diamondop>\<^bsub>G\<^esub> N) \<triangleright> N"
apply (frule smult_sg_nsg[of "H" "N"], assumption+,
       frule nsg_sg[of "N"],
       frule N_sg_HN[of "H" "N"], assumption+,
       frule Gp_smult_sg_nsg[of "H" "N"], assumption+,
       rule Group.cond_nsg[of "\<natural>(H \<diamondop>\<^bsub>G\<^esub> N)" "N"], assumption+)
apply ((rule ballI)+,
       frule_tac a = a in Group.i_closed[of "\<natural>(H \<diamondop>\<^bsub>G\<^esub> N)"], assumption+,
       simp add:Gp_carrier) 

apply (frule r_sub_smult[of "H" "N"], assumption+,
       frule_tac c = h in subsetD[of "N" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+,
       simp add:Gp_mult_induced[of "H \<diamondop>\<^bsub>G\<^esub> N"] sg_i_induced[of "H \<diamondop>\<^bsub>G\<^esub> N"])
apply (frule_tac x = a and y = h in sg_mult_closed[of "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+,
       simp add:Gp_mult_induced)
apply (rule_tac a = a and h = h in nsgPr1_1[of "N"], assumption+,
       frule sg_subset[of "H \<diamondop>\<^bsub>G\<^esub> N"], frule_tac c = a in subsetD[of "H \<diamondop>\<^bsub>G\<^esub> N"
       "carrier G"], assumption+)
done 

lemma (in Group) Gp_smult_nsg1:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> Gp G (N \<diamondop>\<^bsub>G\<^esub> H) \<triangleright> N"
apply (simp add:smult_commute_sg_nsg[THEN sym, of "H" "N"],
       simp only:Gp_smult_nsg)
done

lemma (in Group) ZassenhausTr2_3:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; Gp G H \<triangleright> H1\<rbrakk> \<Longrightarrow> H1 \<subseteq> H"
apply (frule Group_Gp[of "H"],
       frule Group.nsg_sg[of "\<natural>H" "H1"], assumption,
       frule Group.sg_subset[of "\<natural>H" "H1"], assumption, simp add:Gp_carrier)
done

lemma (in Group) ZassenhausTr2_4:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; Gp G H \<triangleright> H1; h \<in> H; 
               h1 \<in> H1\<rbrakk> \<Longrightarrow> h \<cdot> h1 \<cdot> (\<rho> h) \<in> H1" 
apply (frule Group_Gp[of "H"])
apply (frule_tac a = h and h = h1 in Group.nsgPr1_1[of "\<natural>H" "H1"], assumption)
       apply (simp add:Gp_carrier) apply assumption
apply (simp add:Gp_def)
done

lemma (in Group) ZassenhausTr1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1;
       Gp G H \<triangleright> H1; Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1) = (H \<inter> K1) \<diamondop>\<^bsub>G\<^esub> H1"
apply (frule Group_Gp[of "H"],
       frule Group.nsg_sg[of "\<natural>H" "H1"], assumption,
       frule Group.sg_subset[of "\<natural>H" "H1"], assumption, simp add:Gp_carrier)
apply (frule Group_Gp[of "K"],
       frule Group.nsg_sg[of "\<natural>K" "K1"], assumption,
       frule Group.sg_subset[of "\<natural>K" "K1"], assumption, simp add:Gp_carrier)
apply (rule equalityI)
 apply (rule subsetI,
        simp add:s_top_def, (erule bexE)+,
        frule_tac h = xa in sg_subset_elem[of "H1"], assumption+,
        frule_tac h = y in sg_subset_elem[of "H"], simp,
        frule_tac a = y in i_closed,
        frule_tac a = xa and b = y in mult_closed, assumption+,
        frule_tac a1 = y and b1 = "\<rho> y" and c1 = "xa \<cdot> y" in tassoc[THEN sym],
        assumption+)
 apply (frule sym, thin_tac "xa \<cdot> y = x", simp, thin_tac "x = xa \<cdot> y",
        simp add:r_i l_unit,
        frule_tac x = y in sg_i_closed[of "H"], simp) 
 apply (frule_tac a1 = "\<rho> y" and b1 = xa and c1 = y in tassoc[THEN sym],
         assumption+, simp, thin_tac "\<rho> y \<cdot> (xa \<cdot> y) = \<rho> y \<cdot> xa \<cdot> y")
 apply (frule_tac h = "\<rho> y" and ?h1.0 = xa in ZassenhausTr2_4[of "H" "H1"],
                assumption+, simp add:iop_i_i)
 apply blast

 apply (rule subsetI)
 apply (simp add:s_top_def, (erule bexE)+,
        frule_tac h = xa in sg_subset_elem[of "H"], simp,
        frule_tac h = y in sg_subset_elem[of "H1"], assumption,
        frule sym, thin_tac "xa \<cdot> y = x", simp, thin_tac "x = xa \<cdot> y")
apply (frule_tac a = xa in i_closed,
       frule_tac a = xa and b = y in mult_closed, assumption+,
       frule_tac a = "xa \<cdot> y" and b = "\<rho> xa" and c = xa in tassoc, assumption+)
 apply (simp add:l_i r_unit,
       frule_tac h = xa and ?h1.0 = y in ZassenhausTr2_4[of "H" "H1"],
                assumption+, simp, assumption, blast)
done

lemma (in Group) ZassenhausTr1_1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1;
       Gp G H \<triangleright> H1; Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> G \<guillemotright> (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1))"
apply (rule s_top_commute_sg, assumption)
apply (simp add:inter_sgs[of "H" "K1"])
apply (rule ZassenhausTr1 [THEN sym, of "H" "H1" "K" "K1"], assumption+)
done

lemma (in Group) ZassenhausTr2:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; Gp G H \<triangleright> H1\<rbrakk> \<Longrightarrow>
                                  H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K) = (H \<inter> K) \<diamondop>\<^bsub>G\<^esub> H1"
apply (frule special_nsg_G1[of "K"])
apply (simp add: ZassenhausTr1 [of "H" "H1" "K" "K"])
done

lemma (in Group) ZassenhausTr2_1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; Gp G H \<triangleright> H1\<rbrakk>
  \<Longrightarrow> G \<guillemotright> H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)"
apply (frule ZassenhausTr2 [of "H" "H1" "K"], assumption+,
       frule inter_sgs [of "H" "K"], assumption+,
       rule s_top_commute_sg, assumption+)
apply (rule sym, assumption)
done

lemma (in Group) ZassenhausTr2_2:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1;
       Gp G H \<triangleright> H1; Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1) \<subseteq>  H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)"  
apply (frule Group_Gp[of "K"],
       frule Group.nsg_sg[of "\<natural>K" "K1"], assumption,
       frule Group.sg_subset[of "\<natural>K" "K1"], assumption, simp add:Gp_carrier,
       frule Group_Gp[of "H"],
       frule Group.nsg_sg[of "\<natural>H" "H1"], assumption,
       frule Group.sg_subset[of "\<natural>H" "H1"], assumption, simp add:Gp_carrier,
       frule sg_subset[of "H"], frule sg_subset[of "K"])
apply (rule s_top_mono[of "H1" "H \<inter> K" "H1" "H \<inter> K1"],
       rule subset_trans[of "H1" "H" "carrier G"], assumption+,
       blast, simp, blast)
done

lemma (in Group) ZassenhausTr2_5:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
      Gp G K \<triangleright> K1; a\<in> H1; b \<in> H \<inter> K1; c \<in> H1\<rbrakk> \<Longrightarrow>
                      a \<cdot> b \<cdot> c \<in> H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)"
apply (simp, erule conjE)
apply (frule sg_subset_elem[of "H1" "a"], assumption+, 
       frule sg_subset_elem[of "H1" "c"], assumption+,
       frule sg_subset_elem[of "H" "b"], assumption+,
       frule i_closed[of "b"],
       frule mult_closed[of "a" "b"], assumption+,
       frule mult_closed[of "a \<cdot> b" "c"], assumption+,
       frule tassoc[of "a \<cdot> b \<cdot> c" "\<rho> b" "b"], assumption+,
       simp add:l_i r_unit)
apply (rule eq_elem_in[of "a \<cdot> b \<cdot> c \<cdot> \<rho> b \<cdot> b" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1" "a \<cdot> b \<cdot> c"],
       thin_tac "a \<cdot> b \<cdot> c \<cdot> \<rho> b \<cdot> b = a \<cdot> b \<cdot> c",
       frule inter_sgs[of "H" "K1"], assumption+,
       rule s_top_elem[of "H1" "H \<inter> K1" "a \<cdot> b \<cdot> c \<cdot> \<rho> b " "b"], assumption+,
       subst tOp_assocTr42, assumption+,
       frule mult_closed[of "b" "c"], assumption+,
       simp add:tassoc[of "a" "b \<cdot> c" "\<rho> b"])
apply (rule sg_mult_closed[of "H1" "a" "b \<cdot> c \<cdot> \<rho> b"], assumption+,
       rule ZassenhausTr2_4[of "H" "H1" "b" "c"], assumption+) apply blast
apply assumption
done

lemma (in Group) ZassenhausTr2_6:"\<lbrakk>u \<in> carrier G; v \<in> carrier G;  
       x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> 
       (u \<cdot> v) \<cdot> (x \<cdot> y) \<cdot> (\<rho> (u \<cdot> v)) = 
                          u \<cdot> v \<cdot> x \<cdot> (\<rho> v) \<cdot> (v \<cdot> y \<cdot> (\<rho> v)) \<cdot> (\<rho> u)"
apply (simp add:i_ab)
apply (frule i_closed[of "u"], frule i_closed[of "v"])
apply (frule mult_closed[of "u" "v"], assumption+,
       frule mult_closed[of "u \<cdot> v" "x"], assumption+,
       frule mult_closed[of "v" "y"], assumption+,
       frule mult_closed[of "v \<cdot> y" "\<rho> v"], assumption+,
       frule mult_closed[of "u \<cdot> v \<cdot> x" "\<rho> v"], assumption+,
       simp add:tOp_assocTr42[THEN sym, of "u \<cdot> v \<cdot> x \<cdot> \<rho> v " 
                               "v \<cdot> y" "\<rho> v" "\<rho> u"])
apply (frule mult_closed[of "x" "y"], assumption+,
       frule mult_closed[of "u \<cdot> v" "x \<cdot> y"], assumption+)
apply (simp add:tassoc[THEN sym, of "u \<cdot> v \<cdot> (x \<cdot> y)" "\<rho> v" "\<rho> u"])
apply (rule r_mult_eqn[of _ _ "\<rho> u"],
       rule mult_closed[of "u \<cdot> v \<cdot> (x \<cdot> y)" "\<rho> v"], assumption+,
       (rule mult_closed)+, assumption+)
apply (rule r_mult_eqn[of _ _ "\<rho> v"], assumption+,
       (rule mult_closed)+, assumption+)
apply (simp add:tOp_assocTr41[THEN sym, of "u \<cdot> v \<cdot> x" "\<rho> v" "v" "y"],
       simp add:tOp_assocTr42[of "u \<cdot> v \<cdot> x" "\<rho> v" "v" "y"],
       simp add:l_i r_unit)
apply (simp add:tOp_assocTr41)
done

lemma (in Group) ZassenhausTr2_7:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; y \<in> carrier G\<rbrakk>
        \<Longrightarrow> a \<cdot> ( x \<cdot> y) \<cdot> (\<rho> a) = a \<cdot> x \<cdot> (\<rho> a) \<cdot> (a \<cdot> y \<cdot> (\<rho> a))"
apply (frule i_closed[of "a"], 
       frule mult_closed[of "a" "y"], assumption+,
       frule mult_closed[of "a \<cdot> y" "\<rho> a"], assumption+)
apply (simp add:tOp_assocTr41[of "a" "x" "\<rho> a" "a \<cdot> y \<cdot> (\<rho> a)"],
       simp add:tassoc[THEN sym, of "\<rho> a" "a \<cdot> y" "\<rho> a"],
       simp add:tassoc[THEN sym, of "\<rho> a" "a" "y"] l_i l_unit,
       simp add:tOp_assocTr41[THEN sym],
       simp add:tOp_assocTr42[THEN sym])
done

lemma (in Group) ZassenhausTr3:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
              Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow>  Gp G (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)) \<triangleright> (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1))"
apply (frule ZassenhausTr2_1 [of "H" "H1" "K"], assumption+,
       frule ZassenhausTr2_1 [of "H" "H1" "K1"], assumption+,
       frule ZassenhausTr2_2 [of "H" "H1" "K" "K1"], assumption+,
       frule sg_sg [of "H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)" "H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)"], assumption+,
       frule Group_Gp[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"])
apply (rule Group.cond_nsg[of "\<natural>(H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K)" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1"], assumption+,
       (rule ballI)+,
       simp add:Gp_carrier)
 apply (frule_tac c = h in subsetD[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"],
            assumption+,
        simp add:Gp_mult_induced[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"],
        simp add:sg_i_induced[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"],
        frule_tac x = a in sg_i_closed[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"], assumption+,
        frule_tac x = a and y = h in sg_mult_closed[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"], 
        assumption+,
        simp add:Gp_mult_induced[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"],
        thin_tac "\<rho> a \<in> H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K", thin_tac "a \<cdot> h \<in> H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K")
 apply (simp add:s_top_def[of "G" "H1" "H \<inter> K"], (erule bexE)+,
        simp add:s_top_def[of "G" "H1" "H \<inter> K1"], fold s_top_def,
       (erule bexE)+, thin_tac "xa \<cdot> ya = h", (erule conjE)+,
        thin_tac "xa \<in> H1", thin_tac "ya \<in> H",
        frule sym, thin_tac "x \<cdot> y = a", 
        frule sym, thin_tac "xb \<cdot> yb = h", simp, (erule conjE)+,
        thin_tac "a = x \<cdot> y", thin_tac "h = xb \<cdot> yb")
 apply (frule_tac h = x in sg_subset_elem[of "H1"], assumption+,
        frule_tac h = y in sg_subset_elem[of "H"], assumption+,
        frule_tac h = xb in sg_subset_elem[of "H1"], assumption+,
        frule_tac h = yb in sg_subset_elem[of "H"], assumption+,
        subst ZassenhausTr2_6, assumption+)

apply (frule_tac a = y and b = xb in mult_closed, assumption+,
       frule_tac a = y in i_closed,
       frule_tac a = "y \<cdot> xb" and b = "\<rho> y" in mult_closed, assumption+,
       frule_tac a = x and b = "y \<cdot> xb \<cdot> \<rho> y" in mult_closed, assumption+,
       frule_tac a = y and b = yb in mult_closed, assumption+,
       frule_tac a = "y \<cdot> yb" and b = "\<rho> y" in mult_closed, assumption+,
       frule_tac a = "x \<cdot> y \<cdot> xb \<cdot> \<rho> y" and b = "y \<cdot> yb \<cdot> \<rho> y" and c = "\<rho> x" 
        in ZassenhausTr2_5[of "H" "H1" "K" "K1"], assumption+,
       frule_tac a = x and b = y in mult_closed, assumption+,
       frule_tac a = "x \<cdot> y" and b = xb and c = "\<rho> y" in tassoc, assumption+,
       simp, thin_tac "x \<cdot> y \<cdot> xb \<cdot> \<rho> y = x \<cdot> y \<cdot> (xb \<cdot> \<rho> y)",
       frule_tac a = xb and b = "\<rho> y" in mult_closed, assumption+,
              simp add:tassoc)
apply (rule_tac x = x and y = "y \<cdot> (xb \<cdot> \<rho> y)" in sg_mult_closed, assumption+,
       simp add:tassoc[THEN sym],
       rule_tac h = y and ?h1.0 = xb in ZassenhausTr2_4[of "H" "H1"],
            assumption+)
apply (frule_tac x = y and y = yb in sg_mult_closed[of "H"], assumption+,
       frule_tac x = y in sg_i_closed[of "H"], assumption+,
       frule_tac x = "y \<cdot> yb" and y = "\<rho> y" in sg_mult_closed[of "H"], 
       assumption+, simp,
       rule_tac h = y and ?h1.0 = yb in ZassenhausTr2_4[of "K" "K1"],
            assumption+,
       rule_tac x = x in sg_i_closed[of "H1"], assumption+)
apply (simp add:s_top_def[of "G" "H1" "H \<inter> K1"])
done

lemma (in Group) ZassenhausTr3_2:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
              Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> G \<guillemotright> H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)" 
apply (frule s_top_assoc[of "H1" "H \<inter> K1" "H \<inter> K"],
       (simp add:inter_sgs)+,
       frule inter_sgs[of "H" "K1"], assumption+,
       frule inter_sgs[of "H" "K"], assumption+)
 apply (frule K_absorb_HK[of "H \<inter> K1" "H \<inter> K"], assumption+,
        frule ZassenhausTr2_3[of "K" "K1"], assumption+, blast,
        simp, simp add:ZassenhausTr2_1)
done

lemma (in Group) ZassenhausTr3_3:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> (H1 \<inter> K) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1) = (K1 \<inter> H) \<diamondop>\<^bsub>G\<^esub> (K \<inter> H1)"
apply (rule equalityI)
 apply (rule subsetI, simp add:s_top_def, (erule bexE)+)
 apply (frule sym, thin_tac "xa \<cdot> y = x", simp, (erule conjE)+)
 apply (frule_tac h = xa in sg_subset_elem[of "H1"], assumption+,
        frule_tac h = y in sg_subset_elem[of "K1"], assumption+,
        frule_tac a = xa in i_closed,
        frule_tac a = xa and b = y and c = "\<rho> xa" and d = xa in tOp_assocTr41,
        assumption+,
        frule_tac a = xa and b = y in mult_closed, assumption,
        simp add:l_i r_unit)
 apply (frule_tac h = xa and ?h1.0 = y in ZassenhausTr2_4[of "K" "K1"],
        assumption+)
 apply (frule ZassenhausTr2_3[of "H" "H1"], assumption+,
        frule_tac c = xa in subsetD[of "H1" "H"], assumption+)
 apply (frule_tac x = xa and y = y in sg_mult_closed[of "H"], assumption+)
 apply (frule_tac x = xa in sg_i_closed[of "H"], assumption+,
        frule_tac x = "xa \<cdot> y" and y = "\<rho> xa" in sg_mult_closed[of "H"],
                       assumption+)
 apply blast

 apply (rule subsetI, simp add:s_top_def, (erule bexE)+)
 apply (frule sym, thin_tac "xa \<cdot> y = x", simp, (erule conjE)+)
 apply (frule_tac h = xa in sg_subset_elem[of "K1"], assumption+,
        frule_tac h = y in sg_subset_elem[of "H1"], assumption+,
        frule_tac a = xa in i_closed,
        frule_tac a = xa and b = y and c = "\<rho> xa" and d = xa in tOp_assocTr41,
        assumption+,
        frule_tac a = xa and b = y in mult_closed, assumption,
        simp add:l_i r_unit)

 apply (frule_tac h = xa and ?h1.0 = y in ZassenhausTr2_4[of "H" "H1"],
        assumption+)
 apply (frule ZassenhausTr2_3[of "K" "K1"], assumption+)
 apply (frule_tac c = xa in subsetD[of "K1" "K"], assumption+)
 apply (frule_tac x = xa and y = y in sg_mult_closed[of "K"], assumption+)
 apply (frule_tac x = xa in sg_i_closed[of "K"], assumption+,
        frule_tac x = "xa \<cdot> y" and y = "\<rho> xa" in sg_mult_closed[of "K"],
                       assumption+)
 apply blast
done

lemma (in Group) ZassenhausTr3_4:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1; g \<in> H \<inter> K; h \<in> H \<inter> K1\<rbrakk> \<Longrightarrow> g \<cdot> h \<cdot> (\<rho> g) \<in> H \<inter> K1"
apply (simp, (erule conjE)+) 
apply (frule_tac x = g and y = h in sg_mult_closed, assumption+,
       frule_tac x = g in sg_i_closed[of "H"], assumption+,
       simp add:sg_mult_closed[of "H" "g \<cdot> h" "\<rho> g"])
apply (rule ZassenhausTr2_4[of "K" "K1" "g" "h"], assumption+)
done

lemma (in Group) ZassenhausTr3_5:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> (Gp G (H \<inter> K)) \<triangleright> (H1 \<inter> K) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)"
apply (frule inter_sgs[of "H" "K"], assumption,
       frule inter_sgs[of "H1" "K"], assumption,
       frule inter_sgs[of "K" "H"], assumption,
       frule inter_sgs[of "H" "K1"], assumption+)
apply (frule ZassenhausTr3[of "H \<inter> K" "H1 \<inter> K" "K \<inter> H" "H \<inter> K1"],
       assumption+,
       frule ZassenhausTr0[of "K" "K1" "H" "H1"], assumption+,
       simp add:Int_commute,
       frule ZassenhausTr0[of "H" "H1" "K" "K1"], assumption+,
       simp add:Int_commute)
 apply (frule ZassenhausTr2_3 [of "K" "K1"], assumption+,
        frule ZassenhausTr2_3 [of "H" "H1"], assumption+) 
 apply (simp add:Int_commute[of "K" "H"])
 apply (cut_tac Int_mono[of "H" "H" "K1" "K"])
 apply (cut_tac Int_mono[of "H1" "H" "K" "K"])
 apply (simp only:Int_absorb1[of "H \<inter> K1" "H \<inter> K"],
        simp only:K_absorb_HK[of "H1 \<inter> K" "H \<inter> K"]) apply simp+
done

lemma (in Group) ZassenhausTr4:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
     Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)) \<diamondop>\<^bsub>G\<^esub> (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)) = H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)"
apply (frule ZassenhausTr2 [of "H" "H1" "K"], assumption+,
       frule ZassenhausTr2 [of "H" "H1" "K1"], assumption+,
       frule ZassenhausTr1_1 [of "H" "H1" "K" "K1"], assumption+,
       frule ZassenhausTr2_1 [of "H" "H1" "K"], assumption+,
       frule ZassenhausTr2_2 [of "H" "H1" "K" "K1"], assumption+)
apply (rule K_absorb_HK[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"], assumption+)
done

lemma (in Group) ZassenhausTr4_0: "\<lbrakk>G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
     Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow>  H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K) = (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)"
apply (frule inter_sgs [of "H" "K1"], assumption+,
       frule inter_sgs [of "H" "K"], assumption+)
apply (subst s_top_assoc [of "H1" "H \<inter> K1" "H \<inter> K"], assumption+,
       subst K_absorb_HK[of "H \<inter> K1" "H \<inter> K"], assumption+)
apply (frule ZassenhausTr2_3[of "K" "K1"], assumption+,
       rule Int_mono[of "H" "H" "K1" "K"]) 
apply simp+
done

lemma (in Group) ZassenhausTr4_1:"\<lbrakk>G \<guillemotright> H; (Gp G H) \<triangleright> H1; (Gp G H) \<guillemotright> (H \<inter> K)\<rbrakk>
                           \<Longrightarrow> (Gp G (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K))) \<triangleright> H1" 
apply (frule Group_Gp [of "H"],
       frule Group.nsg_sg[of "Gp G H" "H1"], assumption+,
       frule Group.Gp_smult_nsg1[of "\<natural>H" "H \<inter> K" "H1"], assumption+,
       frule subg_sg_sg [of "H" "H1"], assumption+,
       frule Group.sg_subset[of "\<natural>H" "H1"], assumption,
       frule Group.sg_subset[of "\<natural>H" "H \<inter> K"], assumption+,
       frule Group.smult_nsg_sg[of "\<natural>H" "H \<inter> K" "H1"], assumption+,
       frule Group.s_top_sub[of "\<natural>H" "H1" "H \<inter> K"], assumption+)
apply (simp only: Gp_carrier s_top_induced [of "H" "H1" "H \<inter> K"])
apply (frule subg_sg_sg[of "H" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"], assumption+,
       simp add:Gp_inherited[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K" "H"])
done

section "Homomorphism"

lemma gHom: "\<lbrakk>Group F; Group G; f \<in> gHom F G ; x \<in> carrier F; 
           y \<in> carrier F\<rbrakk>  \<Longrightarrow> f (x \<cdot>\<^bsub>F\<^esub> y) = (f x) \<cdot>\<^bsub>G\<^esub> (f y)"
apply (simp add: gHom_def)
done

lemma gHom_mem:"\<lbrakk>Group F; Group G; f \<in> gHom F G ; x \<in> carrier F\<rbrakk> \<Longrightarrow>
                             (f x) \<in> carrier G" 
apply (simp add:gHom_def, (erule conjE)+)
apply (simp add:Pi_def)
done

lemma gHom_func:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
                            f \<in> carrier F \<rightarrow> carrier G"
by (simp add:gHom_def)

(* we have to check the composition of two ghom's *) 
lemma gHomcomp:"\<lbrakk>Group F; Group G; Group H; f \<in> gHom F G; g \<in> gHom G H\<rbrakk> 
    \<Longrightarrow> (g \<circ>\<^bsub>F\<^esub> f) \<in> gHom F H"
apply (simp add:gHom_def)
 apply (erule conjE)+
apply (simp add:cmpghom_def composition)
apply (rule ballI)+
 apply (simp add:compose_def)
 apply (frule_tac x = x in funcset_mem [of "f" "carrier F" "carrier G"],
                                              assumption+) 
apply (frule_tac x = y in funcset_mem [of "f" "carrier F" "carrier G"],
                                              assumption+)
apply (simp add:Group.mult_closed[of "F"])
done

lemma gHom_comp_gsurjec:"\<lbrakk>Group F; Group G; Group H; gsurj\<^bsub>F,G\<^esub> f; 
  gsurj\<^bsub>G,H\<^esub> g\<rbrakk>  \<Longrightarrow> gsurj\<^bsub>F,H\<^esub> (g \<circ>\<^bsub>F\<^esub> f)" 
apply (simp add:gsurjec_def,
       simp add:gHomcomp,
       (erule conjE)+)
 apply (simp add:cmpghom_def,
        simp add:gHom_def, (erule conjE)+,
        rule compose_surj, assumption+)
done

lemma gHom_comp_ginjec:"\<lbrakk>Group F; Group G; Group H; ginj\<^bsub>F,G\<^esub> f; ginj\<^bsub>G,H\<^esub> g\<rbrakk> \<Longrightarrow> 
                          ginj\<^bsub>F,H\<^esub> (g \<circ>\<^bsub>F\<^esub> f)" 
apply (simp add:ginjec_def,
       simp add:gHomcomp,
       simp add:gHom_def,
       (erule conjE)+)
apply (simp add:cmpghom_def,
       simp add:comp_inj)
done

lemma ghom_unit_unit:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
                                                   f (\<one>\<^bsub>F\<^esub>) = \<one>\<^bsub>G\<^esub>"
apply (frule Group.unit_closed[of "F"])
apply (frule gHom [of "F" "G" "f" "\<one>\<^bsub>F\<^esub>" "\<one>\<^bsub>F\<^esub>"], assumption+)
 apply (simp add:Group.l_unit[of "F"])
 apply (frule gHom_mem[of "F" "G" "f" "\<one>\<^bsub>F\<^esub>"], assumption+)
 apply (frule sym)
 apply (rule Group.one_unique[of "G" "f \<one>\<^bsub>F\<^esub>" "f \<one>\<^bsub>F\<^esub>"], assumption+)
done

lemma ghom_inv_inv:"\<lbrakk>Group F; Group G; f \<in> gHom F G ; x \<in> carrier F\<rbrakk> \<Longrightarrow>
   f (\<rho>\<^bsub>F\<^esub> x) = \<rho>\<^bsub>G\<^esub> (f x)"
apply (frule Group.i_closed[of "F" "x"], assumption+,
       frule gHom [of "F" "G" "f" "\<rho>\<^bsub>F\<^esub> x" "x"], assumption+)
apply (simp add:Group.l_i, simp add:ghom_unit_unit)
apply (frule sym,
       frule gHom_mem[of "F" "G" "f" "x"], assumption+ ,
       frule gHom_mem[of "F" "G" "f" "\<rho>\<^bsub>F\<^esub> x"], assumption+,
       rule Group.l_i_unique[THEN sym, of "G" "f x" "f (\<rho>\<^bsub>F\<^esub> x)"], assumption+)
done

lemma ghomTr3:"\<lbrakk>Group F; Group G; f \<in> gHom F G ; x \<in> carrier F;
       y \<in> carrier F; f (x \<cdot>\<^bsub>F\<^esub> (\<rho>\<^bsub>F\<^esub> y)) = \<one>\<^bsub>G\<^esub> \<rbrakk> \<Longrightarrow> f x = f y"
apply (frule Group.i_closed[of "F" "y"], assumption+,
       simp only:gHom ghom_inv_inv)
apply (rule Group.r_div_eq[of "G" "f x" "f y"], assumption,
       (simp add:gHom_mem)+)
done

lemma iim_nonempty:"\<lbrakk>Group F; Group G; f \<in> gHom F G; G \<guillemotright> K\<rbrakk> \<Longrightarrow>
                       (iim F G f K) \<noteq> {}" 
apply (frule Group.sg_unit_closed[of "G" "K"], assumption+,
       frule Group.unit_closed[of "F"])
apply (frule ghom_unit_unit[of "F" "G" "f"], assumption+, simp add:iim_def,
       frule sym, thin_tac "f \<one>\<^bsub>F\<^esub> = \<one>\<^bsub>G\<^esub>", simp)
apply blast
done

lemma ghomTr4:"\<lbrakk>Group F; Group G; f \<in> gHom F G; G \<guillemotright> K\<rbrakk> \<Longrightarrow> 
                  F \<guillemotright> (iim F G f K)"
apply (rule Group.sg_condition[of "F" "iim F G f K"], assumption+,
       rule subsetI, simp add:iim_def,
       simp add:iim_nonempty)
apply ((rule allI)+, rule impI, erule conjE)
apply (simp add:iim_def) apply (erule conjE)+
apply (frule_tac a = b in Group.i_closed[of "F"], assumption+,
       frule_tac a = a and b = "\<rho>\<^bsub>F\<^esub> b" in Group.mult_closed[of "F"],
        assumption+, simp)
apply (simp add:gHom ghom_inv_inv)
apply (frule_tac x = "f b" in Group.sg_i_closed[of "G" "K"], assumption+) 
apply (simp add:gHom_mem Group.sg_mult_closed)
done

lemma (in Group) IdTr0: "idmap (carrier G) \<in> gHom G G"
apply (simp add:gHom_def)
apply (simp add:idmap_def extensional_def)
apply (simp add:Pi_def mult_closed)
done

abbreviation
  IDMAP ("(I\<^bsub>_\<^esub>)" [999]1000) where
   "I\<^bsub>F\<^esub> == idmap (carrier F)"

abbreviation
  INVFUN ("(3Ifn _ _ _)" [88,88,89]88) where
  "Ifn F G f == invfun (carrier F) (carrier G) f"

lemma IdTr1:"\<lbrakk>Group F; x \<in> carrier F\<rbrakk> \<Longrightarrow> (I\<^bsub>F\<^esub>) x = x"
apply (simp add:idmap_def)
done

lemma IdTr2:"Group F \<Longrightarrow> gbij\<^bsub>F,F\<^esub> (I\<^bsub>F\<^esub>)"
apply (simp add:gbijec_def)
apply (rule conjI)
 (* gsurjec *)
  apply (simp add:gsurjec_def)
      apply (rule conjI)
        apply (simp add:idmap_def gHom_def Group.mult_closed)
      apply (simp add:surj_to_def image_def idmap_def)
  (* ginjec *)
  apply (simp add:ginjec_def)
     apply (simp add:idmap_def gHom_def Group.mult_closed)
done

lemma Id_l_unit:"\<lbrakk>Group G; gbij\<^bsub>G,G\<^esub> f\<rbrakk> \<Longrightarrow> I\<^bsub>G\<^esub> \<circ>\<^bsub>G\<^esub> f = f"
apply (rule funcset_eq[of _ "carrier G"])
 apply (simp add:cmpghom_def)
 apply (simp add:gbijec_def gsurjec_def gHom_def)
apply (rule ballI)
 apply (simp add:cmpghom_def compose_def)
 apply (frule_tac x = x in gHom_mem[of "G" "G" "f"], assumption+)
  apply (simp add:gbijec_def gsurjec_def, assumption)
 apply (simp add:IdTr1)
done


section "Gkernel"

lemma gkernTr1:"\<lbrakk>Group F; Group G; f \<in> gHom F G; x \<in> gker\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow>                    x \<in> carrier F"
apply (simp add: gkernel_def)
done 

lemma gkernTr1_1:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> gker\<^bsub>F,G\<^esub> f \<subseteq> carrier F"
by (rule subsetI, simp add:gkernTr1)

lemma gkernTr2:"\<lbrakk>Group F; Group G; f \<in> gHom F G; x \<in> gker\<^bsub>F,G\<^esub> f; y \<in> gker\<^bsub>F,G\<^esub> f\<rbrakk>
   \<Longrightarrow> (x \<cdot>\<^bsub>F\<^esub> y) \<in> gker\<^bsub>F,G\<^esub> f"
apply (simp add:gkernel_def)
apply (simp add:gHom, (erule conjE)+)
apply (simp add:Group.mult_closed, 
       frule Group.unit_closed[of "G"], 
       simp add:Group.l_unit[of "G"])
done

lemma gkernTr3:"\<lbrakk>Group F; Group G; f \<in> gHom F G ; x \<in> gker\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow>
                    (\<rho>\<^bsub>F\<^esub> x) \<in> gker\<^bsub>F,G\<^esub> f"
apply (simp add:gkernel_def)
(* thm ghom_inv_inv [of "F" "G" "f" "x"] *)
apply (simp add:ghom_inv_inv [of "F" "G" "f" "x"])
apply (simp add:Group.i_closed) apply (simp add:Group.i_one)
done

lemma gkernTr6:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> (\<one>\<^bsub>F\<^esub>) \<in> gker\<^bsub>F,G\<^esub> f"
apply (simp add:gkernel_def)   
apply (simp add:Group.unit_closed ghom_unit_unit [of "F" "G" "f" ])
done

lemma gkernTr7:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> F \<guillemotright> gker\<^bsub>F,G\<^esub> f"
apply (rule Group.sg_condition[of "F" "gker\<^bsub>F,G\<^esub> f"], assumption+,
       rule subsetI, simp add:gkernTr1,
       frule gkernTr6[of "F" "G" "f"], assumption+, simp add:nonempty)

apply ((rule allI)+, rule impI, erule conjE,
        frule_tac x = b in gkernTr3[of "F" "G" "f"], assumption+)
apply (simp add:gkernTr2)
done

lemma gker_normal:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> F \<triangleright> gker\<^bsub>F,G\<^esub> f"
apply (rule Group.cond_nsg[of "F" "gker\<^bsub>F,G\<^esub> f"], assumption)
apply (simp add:gkernTr7)
apply (rule ballI)+
apply (simp add:gkernel_def, erule conjE)
apply (frule_tac a = a in Group.i_closed[of "F"], assumption)
apply (subst gHom [of "F" "G" "f" _], assumption+)
       apply (simp add:Group.mult_closed[of "F"])
       apply assumption
apply (simp add:gHom)
 apply (simp add:Group.mult_closed[of "F"])+
 apply (frule_tac x = a in gHom_mem[of "F" "G" "f"], assumption+,
        simp add:Group.r_unit[of "G"]) 
 apply (simp add:ghom_inv_inv, simp add:Group.r_i)
done

lemma Group_coim:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> Group ( F / gker\<^bsub>F,G\<^esub> f)"
by (frule gker_normal[of "F" "G" "f"], assumption+,
       simp add:Group.Group_Qg[of "F" "gker\<^bsub>F,G\<^esub> f"])

lemma gkern1:"\<lbrakk>Group F; Ugp E; f \<in> gHom F E\<rbrakk> \<Longrightarrow> gker\<^bsub>F,E\<^esub> f = carrier F"
apply (frule Group_Ugp[of "E"])
apply (frule gkernTr1_1[of "F" "E" "f"], assumption+)
apply (rule equalityI, assumption)
apply (rule subsetI,
       thin_tac "gker\<^bsub>F,E\<^esub> f \<subseteq> carrier F",
       simp add:gkernel_def,
       frule_tac x = x in gHom_mem[of "F" "E" "f"], assumption+,
       simp add:Ugp_def)
done

lemma gkern2:"\<lbrakk>Group F; Group G; f \<in> gHom F G; ginj\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow>
               gker\<^bsub>F,G\<^esub> f = {\<one>\<^bsub>F\<^esub>}"
apply (frule gkernTr6[of "F" "G" "f"], assumption+,
       frule singleton_sub[of "\<one>\<^bsub>F\<^esub>" "gker\<^bsub>F,G\<^esub> f"],
       rule equalityI)
 apply (rule subsetI,
        thin_tac "{\<one>\<^bsub>F\<^esub>} \<subseteq> gker\<^bsub>F,G\<^esub> f",
        simp add:gkernel_def, (erule conjE)+)
 apply (frule sym, thin_tac "f \<one>\<^bsub>F\<^esub> = \<one>\<^bsub>G\<^esub>", simp, thin_tac "\<one>\<^bsub>G\<^esub> = f \<one>\<^bsub>F\<^esub>",
        simp add:ginjec_def, simp add:inj_on_def)  
apply assumption
done

lemma gkernTr9:"\<lbrakk>Group F; Group G; f \<in> gHom F G; a \<in> carrier F; b \<in> carrier F\<rbrakk>
             \<Longrightarrow>  ((gker\<^bsub>F,G\<^esub> f) \<bullet>\<^bsub>F\<^esub> a = (gker\<^bsub>F,G\<^esub> f) \<bullet>\<^bsub>F\<^esub> b) = (f a = f b)"
(* thm r_cosEqVar1 [of "F" "ker f (F \<rightharpoonup> G) " "a" "b"] *)
apply (frule gkernTr7[of "F" "G" "f"], assumption+)
apply (subst Group.rcs_eq[THEN sym, of "F" "gker\<^bsub>F,G\<^esub> f" "a" "b"], assumption+)
apply (thin_tac "F \<guillemotright> gker\<^bsub>F,G\<^esub> f")
apply (simp add:gkernel_def)
apply (frule Group.i_closed[of "F" "a"], assumption)
       apply (simp add:Group.mult_closed[of "F"])
       apply (simp add:gHom, simp add:ghom_inv_inv)
apply (frule gHom_mem[of "F" "G" "f" "a"], assumption+,
       frule gHom_mem[of "F" "G" "f" "b"], assumption+)
apply (rule iffI)
apply (rule Group.r_div_eq[THEN sym, of "G" "f b" "f a"], assumption+)
apply (simp add:Group.r_i[of "G"])
done 

lemma gkernTr11:"\<lbrakk>Group F; Group G; f \<in> gHom F G ; a \<in> carrier F\<rbrakk> \<Longrightarrow> 
                  (iim F G f {f a}) = (gker\<^bsub>F,G\<^esub> f) \<bullet>\<^bsub>F\<^esub> a"
apply (frule gkernTr7[of "F" "G" "f"], assumption+)
apply (rule equalityI) (** iim F G f {f a} \<subseteq> ker\<^sub>F\<^sub>,\<^sub>Gf \<^sub>F a **)
 apply (rule subsetI,
        simp add:iim_def,
        erule conjE)
 apply (frule_tac a1 = x in gkernTr9[THEN sym, of "F" "G" "f" _ "a"],
            assumption+, simp,
        frule_tac a = x in Group.a_in_rcs[of "F" "gker\<^bsub>F,G\<^esub> f"], assumption+,
        simp)

 apply (rule subsetI)
 apply (simp add:gkernel_def rcs_def iim_def, erule exE, (erule conjE)+,
        rotate_tac -1, frule sym, thin_tac "h \<cdot>\<^bsub>F\<^esub> a = x", simp add:gHom,
        thin_tac "x = h \<cdot>\<^bsub>F\<^esub> a",
        frule gHom_mem[of "F" "G" "f" "a"], assumption+,
        simp add:Group.mult_closed Group.l_unit)
done

lemma gbij_comp_bij:"\<lbrakk>Group F; Group G; Group H; gbij\<^bsub>F,G\<^esub> f; gbij\<^bsub>G,H\<^esub> g\<rbrakk>
                   \<Longrightarrow> gbij\<^bsub>F,H\<^esub> (g \<circ>\<^bsub>F\<^esub> f)"
apply (simp add:gbijec_def)
apply (simp add:gHom_comp_gsurjec gHom_comp_ginjec)
done

lemma gbij_automorph:"\<lbrakk>Group G; gbij\<^bsub>G,G\<^esub> f; gbij\<^bsub>G,G\<^esub> g\<rbrakk>  \<Longrightarrow> 
                            gbij\<^bsub>G,G\<^esub> (g \<circ>\<^bsub>G\<^esub> f)"
apply (simp add:gbij_comp_bij)
done

lemma l_unit_gHom:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> (I\<^bsub>G\<^esub>) \<circ>\<^bsub>F\<^esub> f = f"
apply (simp add:cmpghom_def) 
apply (rule funcset_eq[of _ "carrier F"],
       simp add:compose_def, simp add:gHom_def)

apply (rule ballI,
       simp add:idmap_def compose_def,
       simp add:gHom_mem[of "F" "G" "f"])
done

lemma r_unit_gHom:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> f \<circ>\<^bsub>F\<^esub> (I\<^bsub>F\<^esub>) = f"
apply (simp add:cmpghom_def)
apply (rule funcset_eq[of _ "carrier F"],
       simp add:compose_def, simp add:gHom_def)
apply (rule ballI,
       simp add:idmap_def compose_def) 
done

section "Image"

lemma inv_gHom:"\<lbrakk>Group F; Group G; gbij\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow> (Ifn F G f) \<in> gHom G F"
apply (simp add:gHom_def) 
apply (rule conjI)
 (** Ifn F G f \<in> carrier G \<rightarrow> carrier F **) 
apply (simp add:invfun_def restrict_def extensional_def)
apply (rule conjI)
apply (rule inv_func)
 apply (simp add:gbijec_def gsurjec_def gHom_def)
 apply (simp add:gbijec_def gsurjec_def ginjec_def)+

apply (rule ballI)+ apply (erule conjE)+
apply (frule gHom_func[of "F" "G" "f"], assumption+,
       frule inv_func[of "f" "carrier F" "carrier G"], assumption+)
apply (frule_tac b = x in invfun_mem[of "f" "carrier F" "carrier G"],
                 assumption+,
       frule_tac b = y in invfun_mem[of "f" "carrier F" "carrier G"],
                 assumption+)
apply (frule_tac x = "(Ifn F G f) x" and y = "(Ifn F G f) y" in 
                      gHom[of "F" "G" "f"], assumption+)
apply (simp only:invfun_r)
apply (frule sym, thin_tac "f ((Ifn F G f) x \<cdot>\<^bsub>F\<^esub> (Ifn F G f) y) = x \<cdot>\<^bsub>G\<^esub> y")
apply (frule_tac a = x and b = y in Group.mult_closed[of "G"], assumption+)
apply (frule_tac b = "x \<cdot>\<^bsub>G\<^esub> y" in invfun_r[of "f" "carrier F" 
                        "carrier G"], assumption+)
 apply (frule_tac r = "f ((Ifn F G f) (x \<cdot>\<^bsub>G\<^esub> y))" and s = "x \<cdot>\<^bsub>G\<^esub> y" and t = "f ((Ifn F G f) x \<cdot>\<^bsub>F\<^esub> (Ifn F G f) y)" in trans, assumption+)
 apply (thin_tac "f ((Ifn F G f) (x \<cdot>\<^bsub>G\<^esub> y)) = x \<cdot>\<^bsub>G\<^esub> y",
        thin_tac "x \<cdot>\<^bsub>G\<^esub> y = f ((Ifn F G f) x \<cdot>\<^bsub>F\<^esub> (Ifn F G f) y)")
 apply (frule_tac b = "x \<cdot>\<^bsub>G\<^esub> y" in invfun_mem[of "f" "carrier F" "carrier G"],
         assumption+,
        frule_tac a = "(Ifn F G f) x" and b = "(Ifn F G f) y" in 
         Group.mult_closed[of "F"], assumption+)
 apply (simp add:inj_on_def) 
done

lemma inv_gbijec_gbijec:"\<lbrakk>Group F; Group G; gbij\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow> gbij\<^bsub>G,F\<^esub> (Ifn F G f)"
apply (frule inv_gHom [of "F" "G" "f"], assumption+)
apply (simp add:gbijec_def)
apply (rule conjI)
(* gsurjec *)
apply (simp add:gsurjec_def ginjec_def, (erule conjE)+)
apply (frule gHom_func[of "F" "G" "f"], simp add:invfun_surj,
       assumption+, simp add:invfun_surj)
(* ginjec *)
apply (erule conjE, simp add:gsurjec_def ginjec_def, erule conjE,
       frule gHom_func[of "F" "G" "f"], assumption+,
       rule invfun_inj, assumption+)
done

lemma l_inv_gHom:"\<lbrakk>Group F; Group G; gbij\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow> (Ifn F G f) \<circ>\<^bsub>F\<^esub> f = (I\<^bsub>F\<^esub>)"
apply (rule funcset_eq[of _ "carrier F"],
       simp add:cmpghom_def, simp add:idmap_def,
       rule ballI)
 apply (simp add:idmap_def cmpghom_def compose_def,
        simp add:gbijec_def gsurjec_def ginjec_def, (erule conjE)+,
        frule gHom_func[of "F" "G" "f"], assumption+)
 apply (rule invfun_l, assumption+)
done
  
lemma img_mult_closed:"\<lbrakk>Group F; Group G; f \<in> gHom F G; u \<in> f `(carrier F);
v \<in> f `(carrier F)\<rbrakk> \<Longrightarrow> u \<cdot>\<^bsub>G\<^esub> v \<in> f `(carrier F)" 
apply (simp add:image_def)
apply ((erule bexE)+, simp) 
apply (subst gHom [of "F" "G" "f", THEN sym], assumption+)
apply (frule_tac a = x and b = xa in Group.mult_closed [of "F"], assumption+)
apply blast
done

lemma img_unit_closed:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
                                            \<one>\<^bsub>G\<^esub> \<in> f `(carrier F)"
apply (cut_tac Group.unit_closed[of "F"],
      frule ghom_unit_unit[THEN sym, of "F" "G" "f"], assumption+,
      simp add:image_def, blast,
      assumption)
done

lemma imgTr7:"\<lbrakk>Group F; Group G; f \<in> gHom F G; u \<in> f `(carrier F)\<rbrakk>
  \<Longrightarrow> \<rho>\<^bsub>G\<^esub> u  \<in> f `(carrier F)"
apply (simp add:image_def, erule bexE, simp)
 apply (subst ghom_inv_inv[THEN sym, of "F" "G" "f"], assumption+)
 apply (frule_tac a = x in Group.i_closed[of "F"], assumption+)
 apply blast
done

lemma imgTr8:"\<lbrakk>Group F; Group G; f \<in> gHom F G; F \<guillemotright> H; u \<in> f ` H; 
                v \<in> f` H \<rbrakk> \<Longrightarrow> u \<cdot>\<^bsub>G\<^esub> v \<in> f ` H" 
apply (simp add:image_def, (erule bexE)+, simp,
       subst gHom [of "F" "G" "f" _, THEN sym], assumption+)
 apply (simp only:Group.sg_subset_elem[of "F"],
         simp only:Group.sg_subset_elem[of "F"])
 apply (frule_tac x = x and y = xa in Group.sg_mult_closed[of "F" "H"],
           assumption+)
 apply blast
done

lemma imgTr9:"\<lbrakk>Group F; Group G; f \<in> gHom F G; F \<guillemotright> H; u \<in> f ` H\<rbrakk> \<Longrightarrow> 
                    \<rho>\<^bsub>G\<^esub> u \<in> f ` H" 
apply (simp add:image_def, erule bexE, simp)
apply (frule_tac h = x in Group.sg_subset_elem[of "F" "H"], assumption+,
       simp add:ghom_inv_inv[THEN sym])
apply (frule_tac x = x in Group.sg_i_closed [of "F" "H"], assumption+,
       blast)
done

lemma imgTr10:"\<lbrakk>Group F; Group G; f \<in> gHom F G; F \<guillemotright> H\<rbrakk> \<Longrightarrow> \<one>\<^bsub>G\<^esub> \<in> f ` H"
apply (frule Group.sg_unit_closed[of "F" "H"], assumption+,
       subst ghom_unit_unit[THEN sym, of "F" "G" "f"], assumption+)
apply (simp add:image_def, blast)
done

lemma imgTr11:"\<lbrakk>Group F; Group G; f \<in> gHom F G; F \<guillemotright> H\<rbrakk> \<Longrightarrow> G \<guillemotright> (f ` H)"
apply (frule gHom_func[of "F" "G" "f"], assumption+,
       frule Group.sg_subset[of "F" "H"], assumption+,
       frule image_sub[of "f" "carrier F" "carrier G" "H"], assumption+)
apply (rule Group.sg_condition[of "G" "f ` H"], assumption+,
       frule imgTr10[of "F" "G" "f" "H"], assumption+,
       rule nonempty, assumption)
apply ((rule allI)+, rule impI, erule conjE,
       frule_tac u = b in imgTr9[of "F" "G" "f" "H"], assumption+,
       frule_tac u = a and v = "\<rho>\<^bsub>G\<^esub> b" in imgTr8[of "F" "G" "f"], assumption+)
done

lemma sg_gimg:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk>  \<Longrightarrow> G \<guillemotright> f`(carrier F)"  
apply (frule Group.special_sg_G [of "F"])
apply (simp add:imgTr11)
done

lemma Group_Img:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> Group (Img\<^bsub>F,G\<^esub> f)"
apply (frule sg_gimg [of "F" "G" "f"], assumption+,
       simp add:Gimage_def Group.Group_Gp[of "G"])
done

lemma Img_carrier:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
                         carrier (Img\<^bsub>F,G\<^esub> f) = f ` (carrier F)"
by (simp add:Gimage_def Gp_def)

lemma hom_to_Img:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> f \<in> gHom F (Img\<^bsub>F,G\<^esub> f)"
by (simp add:gHom_def Gimage_def Gp_def)

lemma gker_hom_to_img:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
                               gker\<^bsub>F,(Img\<^bsub>F,G\<^esub> f)\<^esub> f = gker\<^bsub>F,G\<^esub> f" 
by (simp add:gkernel_def Gimage_def,
       frule sg_gimg[of "F" "G" "f"], assumption+,
       simp add:Group.one_Gp_one[of "G" "f ` (carrier F)"])

lemma Pj_im_subg:"\<lbrakk>Group G; G \<guillemotright> H; G \<triangleright> K; K \<subseteq> H\<rbrakk> \<Longrightarrow> 
                         Pj G K ` H = carrier ((Gp G H) / K)"
apply (simp add: Qg_def [of "Gp G H" "K"])
apply (rule equalityI)
   apply (simp add: Pj_def set_rcs_def Group.sg_subset_elem cong: image_cong_simp)
  using Group.Gp_rcs Group.carrier_Gp Group.nsg_sg apply fastforce
apply (rule subsetI)
 apply (simp add:image_def Pj_def)
 apply (simp add:set_rcs_def)
 apply (simp add:Group.Gp_carrier, erule bexE)
  apply (frule Group.nsg_sg[of "G" "K"], assumption+)
 apply (frule_tac x = a in Group.Gp_rcs[of "G" "K" "H"], assumption+,
        simp)
 apply (frule_tac h = a in Group.sg_subset_elem[of "G" "H"], assumption+)  
 apply blast
done

lemma (in Group) subg_Qsubg:"\<lbrakk>G \<guillemotright> H; G \<triangleright> K; K \<subseteq> H\<rbrakk> \<Longrightarrow> 
                            (G / K) \<guillemotright>  carrier ((Gp G H) / K)"
apply (frule Pj_ghom[of "K"])
apply (frule nsg_sg [of "K"])
apply (frule Group_Qg[of "K"])
apply (cut_tac imgTr11 [of "G" "G / K" "Pj G K" "H"])
apply (cut_tac Pj_im_subg [of "G" "H" "K"])
apply simp apply (rule Group_axioms | assumption)+
done

section "Induced homomorphisms"

lemma inducedhomTr:"\<lbrakk>Group F; Group G; f \<in> gHom F G; 
  S \<in> set_rcs F (gker\<^bsub>F,G\<^esub> f); s1 \<in> S; s2 \<in> S \<rbrakk> \<Longrightarrow> f s1 = f s2"
apply (simp add:set_rcs_def, erule bexE) 
apply (frule_tac a1 = a in gkernTr11[THEN sym, of "F" "G" "f"], assumption+,
       simp, thin_tac "S = iim F G f {f a}",
       thin_tac "gker\<^bsub>F,G\<^esub> f \<bullet>\<^bsub>F\<^esub> a = iim F G f {f a}")
apply (simp add:iim_def)
done

definition
  induced_ghom :: "[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme, 
                ('a  \<Rightarrow> 'b)] \<Rightarrow> ('a set  \<Rightarrow> 'b )" where
  "induced_ghom F G f = (\<lambda>X\<in> (set_rcs F (gker\<^bsub>F,G\<^esub> f)). f (SOME  x. x \<in> X))"

abbreviation
  INDUCED_GHOM :: "['a \<Rightarrow> 'b, ('a, 'm) Group_scheme, ('b, 'm1) Group_scheme]
    \<Rightarrow>  ('a set  \<Rightarrow> 'b )" ("(3_\<dieresis>\<^bsub>_,_\<^esub>)" [82,82,83]82) where
  "f\<dieresis>\<^bsub>F,G\<^esub> == induced_ghom F G f"

lemma induced_ghom_someTr:"\<lbrakk>Group F; Group G; f \<in> gHom F G; 
X \<in> set_rcs F (gker\<^bsub>F,G\<^esub> f)\<rbrakk> \<Longrightarrow> f (SOME xa. xa \<in> X) \<in> f `(carrier F)"
apply (simp add:set_rcs_def, erule bexE, simp)
apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
apply (rule someI2_ex)
apply (frule_tac a = a in Group.a_in_rcs[of "F" "gker\<^bsub>F,G\<^esub> f"], assumption+) 
apply blast
 apply (frule_tac a = a and x = x in Group.rcs_subset_elem[of "F" "gker\<^bsub>F,G\<^esub> f"],
        assumption+)
 apply (simp add:image_def, blast)
done

lemma induced_ghom_someTr1:"\<lbrakk>Group F; Group G; f \<in> gHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
         f (SOME xa. xa \<in> (gker\<^bsub>F,G\<^esub> f) \<bullet>\<^bsub>F\<^esub> a) = f a"
apply (rule someI2_ex)
 apply (frule gkernTr7 [of "F" "G" "f"], assumption+)
 apply (frule Group.a_in_rcs [of "F" "gker\<^bsub>F,G\<^esub> f" "a"], assumption+)
 apply blast
 apply (simp add:gkernTr11 [THEN sym])
 apply (simp add:iim_def)
done

lemma inducedHOMTr0:"\<lbrakk>Group F; Group G; f \<in> gHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
     (f\<dieresis>\<^bsub>F,G\<^esub>) ((gker\<^bsub>F,G\<^esub> f) \<bullet>\<^bsub>F\<^esub> a) = f a"
apply (simp add:induced_ghom_def)
apply (frule gkernTr7[of "F" "G" "f"], assumption+)
 apply (simp add:Group.rcs_in_set_rcs[of "F"])
 apply (simp add:induced_ghom_someTr1)
done

lemma inducedHOMTr0_1:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
                        (f\<dieresis>\<^bsub>F,G\<^esub>) \<in>  set_rcs F (gker\<^bsub>F,G\<^esub> f) \<rightarrow> carrier G" 
apply (rule Pi_I)
 apply (simp add:set_rcs_def, erule bexE, simp)
 apply (subst inducedHOMTr0[of "F" "G" "f"], assumption+)
 apply (simp add:gHom_mem)
done

lemma inducedHOMTr0_2:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow>
    (f\<dieresis>\<^bsub>F,G\<^esub>) \<in> set_rcs F (gker\<^bsub>F,G\<^esub> f) \<rightarrow> f ` (carrier F)"
apply (rule Pi_I)
 apply (simp add:set_rcs_def, erule bexE, simp)
 apply (subst inducedHOMTr0[of "F" "G" "f"], assumption+)
 apply (simp add:image_def, blast)
done

lemma inducedHom:"\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> 
                         (f\<dieresis>\<^bsub>F,G\<^esub>) \<in> gHom (F/(gker\<^bsub>F,G\<^esub> f)) G"
apply (simp add: gHom_def [of "F/ gker\<^bsub>F,G\<^esub> f" "G"])
apply (rule conjI)
apply (simp add:induced_ghom_def extensional_def)
 apply (rule allI) apply (rule impI)+ apply (simp add:Qg_def)

apply (rule conjI)
 apply (simp add:Qg_def inducedHOMTr0_1)
apply (rule ballI)+ 
apply (simp add:Qg_def set_rcs_def, (erule bexE)+)
apply simp
 apply (frule gker_normal[of "F" "G" "f"], assumption+)
 apply (simp add:Group.c_top_welldef [THEN sym, of "F" "gker\<^bsub>F,G\<^esub> f"])
 apply (frule_tac a = a and b = aa in Group.mult_closed[of "F"], assumption+)
 apply (simp add:inducedHOMTr0)
apply (simp add:gHom)
done

lemma induced_ghom_ginjec: "\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
            ginj\<^bsub>(F/(gker\<^bsub>F,G\<^esub> f)),G\<^esub> (f\<dieresis>\<^bsub>F,G\<^esub>)"
apply (simp add:ginjec_def)
apply (simp add:inducedHom)
apply (simp add:inj_on_def)
apply (rule ballI)+
apply (simp add:Qg_def)
apply (simp add:set_rcs_def)
apply ((erule bexE)+, rule impI, simp)
apply (simp add:inducedHOMTr0)
apply (simp add: gkernTr11[THEN sym])
done

lemma inducedhomgsurjec:"\<lbrakk>Group F; Group G; gsurj\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow>
                                gsurj\<^bsub>(F/(gker\<^bsub>F,G\<^esub> f)),G\<^esub> (f\<dieresis>\<^bsub>F,G\<^esub>)"
apply (simp add:gsurjec_def)
apply (simp add:inducedHom)
 apply (erule conjE)
 apply (frule gHom_func[of "F" "G" "f"], assumption+)
 apply (rule surj_to_test)
 apply (simp add:Qg_def)
 apply (frule inducedHOMTr0_2[of "F" "G" "f"], assumption+)
 apply (simp add:surj_to_def[of "f" "carrier F" "carrier G"])

apply (rule ballI)
 apply (simp add:surj_to_def[of "f" "carrier F" "carrier G"],
        frule sym, thin_tac "f ` carrier F = carrier G", simp,
        thin_tac "carrier G = f ` carrier F")
 apply (simp add:image_def, erule bexE, simp,
        thin_tac "b = f x")
 apply (simp add:Qg_def)
 apply (frule_tac a = x in inducedHOMTr0[of "F" "G" "f"], assumption+)
 apply (frule gkernTr7[of "F" "G" "f"], assumption+)
 apply (frule_tac a = x in Group.rcs_in_set_rcs[of "F" "gker\<^bsub>F,G\<^esub> f"],
                              assumption+)
 apply blast
done

lemma homomtr: "\<lbrakk>Group F; Group G; f \<in> gHom F G\<rbrakk> \<Longrightarrow> 
                  (f\<dieresis>\<^bsub>F,G\<^esub>) \<in> gHom (F / (gker\<^bsub>F,G\<^esub> f)) (Img\<^bsub>F,G\<^esub> f)"
apply (simp add:gHom_def [of "F / (gker\<^bsub>F,G\<^esub> f)" _])
apply (rule conjI)
apply (simp add:induced_ghom_def extensional_def)
 apply (rule allI, (rule impI)+, simp add:Qg_def)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Gimage_def Qg_def Gp_def, simp add:set_rcs_def, erule bexE)
 apply simp
 apply (simp add:inducedHOMTr0)

apply (rule ballI)+
 apply (simp add:Qg_def set_rcs_def, (erule bexE)+, simp)
 apply (frule gker_normal[of "F" "G" "f"], assumption+)
 apply (simp add:Group.c_top_welldef[THEN sym, of "F" "gker\<^bsub>F,G\<^esub> f"])
 apply (frule_tac a = a and b = aa in Group.mult_closed[of "F"], assumption+)
 apply (simp add:inducedHOMTr0)
 apply (simp add:Gimage_def)
 apply (subst Group.Gp_mult_induced[of "G" "f ` carrier F"], assumption+)
  apply (simp add:sg_gimg)
  apply (simp add:image_def, blast)
  apply (simp add:image_def, blast)
apply (simp add:gHom)
done

lemma homom2img: "\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow> 
   (f\<dieresis>\<^bsub>F,(Img\<^bsub>F,G\<^esub> f)\<^esub>) \<in> gHom (F / (gker\<^bsub>F,G\<^esub> f)) (Img\<^bsub>F,G\<^esub> f)"
apply (frule hom_to_Img[of "F" "G" "f"], assumption+)
apply (frule inducedHom[of "F" "Img\<^bsub>F,G\<^esub> f" "f"])
 apply (simp add:Group_Img) apply assumption
 apply (simp add:gker_hom_to_img[of "F" "G" "f"])
done

lemma homom2img1:"\<lbrakk>Group F; Group G; f \<in> gHom F G; X \<in> set_rcs F (gker\<^bsub>F,G\<^esub> f)\<rbrakk>
 \<Longrightarrow> (f\<dieresis>\<^bsub>F,(Img\<^bsub>F,G\<^esub> f)\<^esub>) X = (f\<dieresis>\<^bsub>F,G\<^esub>) X"
apply (frule gker_hom_to_img [of "F" "G" "f"], assumption+)
apply (simp add:induced_ghom_def)
done

subsection "Homomorphism therems"

definition
  iota :: "('a, 'm) Group_scheme \<Rightarrow> ('a \<Rightarrow> 'a)"  
(* should be used exclusively as an inclusion map *)
          ("(\<iota>\<^bsub>_\<^esub>)" [1000]999) where
  "\<iota>\<^bsub>F\<^esub> = (\<lambda>x \<in> carrier F. x)"

lemma iotahomTr0:"\<lbrakk>Group G; G \<guillemotright> H; h \<in> H \<rbrakk> \<Longrightarrow> (\<iota>\<^bsub>(Gp G H)\<^esub>) h = h"
apply (simp add:iota_def)
apply (simp add:Gp_def)
done
     
lemma iotahom:"\<lbrakk>Group G; G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> 
                \<iota>\<^bsub>(Gp G H)\<^esub> \<in> gHom (Gp G H) (Gp G (H \<diamondop>\<^bsub>G\<^esub> N))" 
apply (simp add:gHom_def)
apply (rule conjI)
 apply (simp add:iota_def extensional_def)
apply (rule conjI)
apply (simp add:Pi_def restrict_def iota_def)
 apply (rule allI, rule impI)
 apply (simp add:Gp_def)
 apply (frule Group.nsg_sg[of "G" "N"], assumption+) 
 apply (frule Group.l_sub_smult[of "G" "H" "N"], assumption+, 
                                                   simp add: subsetD)
apply (rule ballI)+
 apply (simp add:iota_def, simp add:Group.Gp_carrier)
 apply (frule Group.smult_sg_nsg[of "G" "H" "N"], assumption+,
        frule Group.l_sub_smult[of "G" "H" "N"], assumption+,
        simp add:Group.nsg_sg,
        frule_tac c = x in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+,
        frule_tac c = y in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+)
 apply (simp add:Group.Gp_mult_induced[of "G"])
  apply (simp add:Group.sg_mult_closed)
done

lemma iotaTr0: "\<lbrakk>Group G; G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> 
               ginj\<^bsub>(Gp G H),(Gp G (H \<diamondop>\<^bsub>G\<^esub> N))\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>)"
apply (simp add:ginjec_def)
apply (simp add:iotahom)
apply (simp add:inj_on_def iota_def Gp_def)
done

theorem homomthm1:"\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
     gbij\<^bsub>(F/ (gkernel F G f)), (Gimage F G f)\<^esub> (f\<dieresis>\<^bsub>F, (Gimage F G f)\<^esub>)"
apply (frule homom2img [of "F" "G" "f"], assumption+)
apply (simp add:gbijec_def)
apply (frule hom_to_Img [of "F" "G" "f"], assumption+)
apply (frule Group_coim[of "F" "G" "f"], assumption+,
       frule gHom_func[of "F / (gker\<^bsub>F,G\<^esub> f)" "Img\<^bsub>F,G\<^esub> f" 
        "f\<dieresis>\<^bsub>F,Img\<^bsub>F,G\<^esub> f\<^esub>"], simp add:Group_Img, assumption)
apply (rule conjI)
 (** gsurjec **)  
 apply (simp add:gsurjec_def,
        rule surj_to_test[of "f\<dieresis>\<^bsub>F,Img\<^bsub>F,G\<^esub> f\<^esub>" 
        "carrier (F / gker\<^bsub>F,G\<^esub> f)" "carrier (Img\<^bsub>F,G\<^esub> f)"], assumption+,
        rule ballI)
 apply (thin_tac "f\<dieresis>\<^bsub>F,Img\<^bsub>F,G\<^esub> f\<^esub> \<in> gHom (F / gker\<^bsub>F,G\<^esub> f)
                        (Img\<^bsub>F,G\<^esub> f)") 
 apply (simp add:Img_carrier, simp add:image_def, erule bexE, simp,
        simp add:Qg_def,
        frule gkernTr7[of "F" "G" "f"], assumption+)
 apply (frule_tac a = x in Group.rcs_in_set_rcs[of "F" "gker\<^bsub>F,G\<^esub> f"],
               assumption+)
 apply (simp add:homom2img1) 
 apply (frule_tac a = x in inducedHOMTr0[of "F" "G" "f"], assumption+)
 apply blast  (** gsurjec done **)
(** ginjec **)
apply (frule induced_ghom_ginjec[of "F" "G" "f"], assumption+)
 apply (simp add:ginjec_def) 
 apply (frule conjunct2)
  apply (thin_tac "f\<dieresis>\<^bsub>F,G\<^esub> \<in> gHom (F / gker\<^bsub>F,G\<^esub> f) G \<and>
     inj_on (f\<dieresis>\<^bsub>F,G\<^esub>) (carrier (F / gker\<^bsub>F,G\<^esub> f))")
 apply (simp add:inj_on_def)
apply ((rule ballI)+, rule impI) 
apply (simp add:Qg_def, fold Qg_def)
apply (simp add:homom2img1) 
done

lemma isomTr0 [simp]:"Group F \<Longrightarrow> F \<cong> F"
by (frule IdTr2 [of "F"], simp add:isomorphic_def,
       blast)

lemma isomTr1:"\<lbrakk>Group F; Group G; F \<cong>  G \<rbrakk> \<Longrightarrow> G \<cong> F"
apply (simp add:isomorphic_def, erule exE)
apply (frule_tac f = f in inv_gbijec_gbijec[of "F" "G"], assumption+)
apply blast
done
 
lemma isomTr2:"\<lbrakk>Group F; Group G; Group H; F \<cong> G; G \<cong> H \<rbrakk> \<Longrightarrow> F \<cong> H"
apply (simp add:isomorphic_def)
apply (erule exE)+
apply (simp add:gbijec_def)
 apply (erule conjE)+
apply (frule gHom_comp_gsurjec [of "F" "G" "H" _ _], assumption+)
apply (frule gHom_comp_ginjec [of "F" "G" "H" _ _], assumption+)
apply blast
done
 
lemma gisom1: "\<lbrakk>Group F; Group G; f \<in> gHom F G \<rbrakk> \<Longrightarrow>
     (F/ (gker\<^bsub>F,G\<^esub> f)) \<cong> (Img\<^bsub>F,G\<^esub> f)"
apply (simp add:isomorphic_def)
apply (frule homomthm1 [of "F" "G" "f"], assumption+)
apply blast
done

lemma homomth2Tr0: "\<lbrakk>Group F; Group G; f \<in> gHom F G; G \<triangleright> N\<rbrakk> \<Longrightarrow>   
                           F \<triangleright> (iim F G f N)"
apply (frule Group.cond_nsg[of "F" "iim F G f N"],
       frule Group.nsg_sg[of "G" "N"], assumption+,
       simp add:ghomTr4[of "F" "G" "f" "N"])
apply ((rule ballI)+,
       simp add:iim_def, erule conjE,
       frule_tac a = a in Group.i_closed[of "F"], assumption+,
       frule_tac a = a and b = h in Group.mult_closed[of "F"], assumption+)
 apply (simp add:gHom ghom_inv_inv Group.mult_closed)
apply (frule_tac x = a in gHom_mem[of "F" "G" "f"], assumption+,
       simp add:Group.nsgPr1_1,
       assumption)
done

lemma kern_comp_gHom:"\<lbrakk>Group F; Group G; gsurj\<^bsub>F,G\<^esub> f; G \<triangleright> N\<rbrakk> \<Longrightarrow>
                  gker\<^bsub>F, (G/N)\<^esub> ((Pj G N) \<circ>\<^bsub>F\<^esub> f) = iim F G f N"
apply (simp add:gkernel_def iim_def)
apply (simp add:Group.Qg_one[of "G" "N"] cmpghom_def compose_def)
apply (rule equalityI)
 apply (rule subsetI, simp, erule conjE, simp)
 apply (simp add:gsurjec_def, frule conjunct1, fold gsurjec_def)
 apply (frule_tac x = x in gHom_mem[of "F" "G" "f"], assumption+)
 apply (simp add:Group.Pj_mem[of "G" "N"])
 apply (frule Group.nsg_sg[of "G" "N"], assumption+)
 apply (frule_tac a = "f x" in Group.a_in_rcs[of "G" "N"], assumption+)
 apply simp
apply (rule subsetI)
 apply (simp, erule conjE)
 apply (frule Group.nsg_sg[of "G" "N"], assumption,
        frule_tac h = "f x" in Group.sg_subset_elem[of "G" "N"], assumption+)
 apply (simp add:Group.Pj_mem[of "G" "N"])
 apply (simp add:Group.rcs_fixed2[of "G" "N"])
done

lemma QgrpUnit_1:"\<lbrakk>Group G; Ugp E; G \<triangleright> H; (G / H) \<cong> E \<rbrakk> \<Longrightarrow> carrier G = H"
apply (simp add:isomorphic_def, erule exE)
apply (frule Group.Group_Qg[of "G" "H"], assumption+,
       simp add:gbijec_def, erule conjE)
apply (frule_tac f = f in gkern2[of "G / H" "E"],
       simp add:Ugp_def, simp add:gsurjec_def, assumption,
       simp add:gsurjec_def, frule conjunct1, fold gsurjec_def,
       frule_tac f = f in gkern1[of "G/H" "E"], assumption+)
 apply (simp, thin_tac "gker\<^bsub>(G / H),E\<^esub> f = {\<one>\<^bsub>G / H\<^esub>}",
        thin_tac "gsurj\<^bsub>(G / H),E\<^esub> f", thin_tac "ginj\<^bsub>(G / H),E\<^esub> f",
        thin_tac "Group (G / H)", thin_tac "f \<in> gHom (G / H) E",
        simp add:Group.Qg_carrier)
apply (rule contrapos_pp, simp+,
       frule Group.nsg_sg[of "G" "H"], assumption+,
       frule Group.sg_subset[of "G" "H"], assumption+,
       frule sets_not_eq[of "carrier G" "H"], assumption, erule bexE,
       frule_tac a = a in Group.rcs_in_set_rcs[of "G" "H"], assumption+,
       simp)
 apply (thin_tac "set_rcs G H = {\<one>\<^bsub>G / H\<^esub>}", simp add:Qg_def,
        frule_tac a = a in Group.a_in_rcs[of "G" "H"], assumption+,
        simp)
done
    
lemma QgrpUnit_2:"\<lbrakk>Group G; Ugp E; G \<triangleright> H; carrier G = H\<rbrakk> \<Longrightarrow> (G/H) \<cong> E"
apply (frule Group.Group_Qg [of "G" "H"], assumption+)
apply (simp add:Group.Qg_unit_group[THEN sym, of "G" "H"])
apply (simp add:Ugp_def)
apply (frule Group.Qg_carrier[of "G" "H"], simp) 
apply (thin_tac "set_rcs G H = {H}")
 apply (frule Group.Qg_one[of "G" "H"], assumption+, erule conjE) 
 apply (rule Ugps_isomorphic[of "G / H" "E"])
 apply (simp add:Ugp_def)+
done

lemma QgrpUnit_3:"\<lbrakk>Group G; Ugp E; G \<guillemotright> H; G \<guillemotright> H1; (Gp G H) \<triangleright> H1;
                    ((Gp G H) / H1) \<cong> E \<rbrakk> \<Longrightarrow> H = H1"
apply (frule Group.Group_Gp[of "G" "H"], assumption+)
apply (frule QgrpUnit_1 [of "Gp G H" "E" "H1"], assumption+)
apply (simp add:Group.Gp_carrier)
done

lemma QgrpUnit_4:"\<lbrakk>Group G; Ugp E; G \<guillemotright> H; G \<guillemotright> H1; (Gp G H) \<triangleright> H1;
\<not> ((Gp G H) / H1) \<cong> E \<rbrakk> \<Longrightarrow> H \<noteq> H1"
apply (frule Group.Group_Gp[of "G" "H"], assumption+)
apply (rule contrapos_pp, simp) apply simp
apply (frule QgrpUnit_2 [of "Gp G H1" "E" "H1"], assumption+)
apply (simp add:Group.Gp_carrier)
apply simp
done

definition
  Qmp :: "[('a, 'm) Group_scheme, 'a set, 'a set] \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Qmp G H N = (\<lambda>X\<in> set_rcs G H. {z. \<exists> x \<in> X. \<exists> y \<in> N. (y \<cdot>\<^bsub>G\<^esub> x = z)})"
  
abbreviation
  QP :: "[_, 'a set, 'a set] \<Rightarrow> ('a set \<Rightarrow> 'a set)"
    ("(3Qm\<^bsub>_ _,_\<^esub>)" [82,82,83]82) where
  "Qm\<^bsub>G H,N\<^esub> == Qmp G H N"

 (* "\<lbrakk> Group G; G \<triangleright> H; G \<triangleright> N; H \<subseteq> N \<rbrakk> \<Longrightarrow>
           Qmp\<^bsub>G H,N\<^esub>  \<in> gHom (G / H) (G / N)"  *)

  (* show Qmp G H N is a welldefined map from G/H to G/N. step1 *)

lemma (in Group) QmpTr0:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; H \<subseteq> N ; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                                          Qmp G H N (H \<bullet> a) = (N \<bullet> a)"
apply (frule_tac a = a in rcs_in_set_rcs[of "H"], assumption,
       simp add:Qmp_def)
apply (rule equalityI)
 apply (rule subsetI, simp, (erule bexE)+,
        thin_tac "H \<bullet> a \<in> set_rcs G H",
        simp add:rcs_def, erule bexE)
 apply (frule sym, thin_tac "y \<cdot> xa = x", frule sym, thin_tac "h \<cdot> a = xa",
        simp,
        frule_tac h = y in sg_subset_elem[of "N"], assumption+,
        frule_tac h = h in sg_subset_elem[of "H"], assumption+,
        frule_tac c = h in subsetD[of "H" "N"], assumption+,
        frule_tac x = y and y = h in sg_mult_closed[of "N"], assumption+,
        subst tassoc[THEN sym], assumption+, blast)

apply (rule subsetI,
       thin_tac "H \<bullet> a \<in> set_rcs G H",
       simp add:rcs_def, erule bexE,
       frule sg_unit_closed[of "H"],
       frule l_unit[of "a"], blast) 
done

  (* show Qmp G H N is a welldefined map from G/H to G/N. step2 *)
lemma (in Group) QmpTr1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; H \<subseteq> N; a \<in> carrier G; b \<in> carrier G; 
                      H \<bullet> a = H \<bullet> b\<rbrakk> \<Longrightarrow> N \<bullet> a = N \<bullet> b"
apply (simp add:rcs_eq[THEN sym, of "H" "a" "b"],
       frule subsetD[of "H" "N" "b \<cdot> \<rho> a"], assumption+,
       simp add:rcs_eq[of "N" "a" "b"])
done
   
lemma (in Group) QmpTr2:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; H \<subseteq> N ; X \<in> carrier (G/H)\<rbrakk>
                        \<Longrightarrow> (Qmp G H N) X \<in> carrier (G/N)" 
by (simp add:Qg_carrier[of "H"] set_rcs_def, erule bexE, simp add: QmpTr0,
       simp add:Qg_carrier rcs_in_set_rcs)

lemma (in Group) QmpTr2_1:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> N; H \<subseteq> N \<rbrakk> \<Longrightarrow> 
                           Qmp G H N \<in> carrier (G/H) \<rightarrow> carrier (G/N)"
by (simp add:QmpTr2 [of "H" "N"])

lemma (in Group) QmpTr3:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N; X \<in> carrier (G/H); 
       Y \<in> carrier (G/H)\<rbrakk> \<Longrightarrow> 
     (Qmp G H N) (c_top G H X Y) = c_top G N ((Qmp G H N) X) ((Qmp G H N) Y)" 
apply (frule nsg_sg[of "H"], frule nsg_sg[of "N"])
apply (simp add:Qg_carrier)
apply (simp add:set_rcs_def, (erule bexE)+, simp)
apply (subst c_top_welldef [THEN sym], assumption+)
apply (frule_tac  a = a and b = aa in mult_closed, assumption+)
apply (simp add:QmpTr0)+
apply (subst c_top_welldef [THEN sym], assumption+)
apply simp
done
 
lemma (in Group) Gp_s_mult_nsg:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N; a \<in> N \<rbrakk> \<Longrightarrow>
                                 H \<bullet>\<^bsub>(Gp G N)\<^esub> a =  H \<bullet> a"
by (frule nsg_sg[of "H"], frule nsg_sg[of "N"], 
                          rule Gp_rcs[of "H" "N" "a"], assumption+)

lemma (in Group) QmpTr5:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N; X \<in> carrier (G/H); 
      Y \<in> carrier (G/H) \<rbrakk> \<Longrightarrow> (Qmp G H N) ( X \<cdot>\<^bsub>(G / H)\<^esub> Y) =
                              ((Qmp G H N) X) \<cdot>\<^bsub>(G / N)\<^esub> ((Qmp G H N) Y)"
by (frule nsg_sg[of "H"], frule nsg_sg[of "N"],
       (subst Qg_def)+, simp,
       simp add:QmpTr3 [of "H" "N" "X" "Y"])

lemma (in Group) QmpTr:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N \<rbrakk> \<Longrightarrow>
                            (Qm\<^bsub>G H,N\<^esub>) \<in> gHom (G / H) (G / N)"
apply (simp add:gHom_def)
apply (rule conjI)  
 apply (simp add:Qmp_def extensional_def)
apply (rule allI, (rule impI)+, simp add:Qg_def) 
apply (rule conjI) 
 apply (rule QmpTr2_1[of "H" "N"])
 apply (simp add:nsg_sg)+
apply (rule ballI)+ 
 apply (simp add:QmpTr5)
done
     
lemma (in Group) Qmpgsurjec:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N \<rbrakk> \<Longrightarrow> 
                                      gsurj\<^bsub>(G / H),(G / N)\<^esub> (Qm\<^bsub>G H,N\<^esub>)"
apply (frule nsg_sg[of "H"], frule nsg_sg[of "N"])  
apply (frule QmpTr [of "H" "N"], assumption+) 
apply (simp add:gsurjec_def)
apply (rule surj_to_test)
 apply (simp add:QmpTr2_1)
apply (rule ballI)
 apply (simp add:Qg_carrier,
        simp add:set_rcs_def[of "G" "N"], erule bexE,
        frule_tac a = a in QmpTr0[of "H" "N"], assumption+, simp)
 apply (frule_tac a = a in rcs_in_set_rcs[of "H"], assumption+,
        blast)
done

lemma (in Group) gkerQmp:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N \<rbrakk> \<Longrightarrow>
               gker\<^bsub>(G / H),(G / N)\<^esub> (Qm\<^bsub>G H,N\<^esub>) = carrier ((Gp G N)/ H)"   
apply (frule nsg_sg[of "H"], frule nsg_sg[of "N"])
apply (simp add:gkernel_def)
apply (rule equalityI)
 apply (rule subsetI,
        simp add:Qg_carrier set_rcs_def, erule conjE, erule bexE, simp,
        simp add:Qg_one) 
 apply (simp add:QmpTr0,
        frule_tac a = a in a_in_rcs[of "N"], assumption+, simp,
        frule Group_Gp[of "N"])
 apply (simp add:Group.Qg_carrier, simp add:set_rcs_def, simp add:Gp_carrier,
        simp add:Gp_rcs, blast)

apply (rule subsetI)
 apply (frule Group_Gp[of "N"],
        simp add:Group.Qg_carrier Qg_one set_rcs_def, erule bexE,
        simp add:Qg_carrier, thin_tac "x = H \<bullet>\<^bsub>\<natural>N\<^esub> a")
 apply (simp add:Gp_carrier, simp add:Gp_rcs,
        frule_tac h = a in sg_subset_elem[of "N"], assumption,
        simp add:rcs_in_set_rcs, simp add:QmpTr0,
        simp add:rcs_fixed2[of "N"])
done

theorem (in Group) homom2:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N\<rbrakk> \<Longrightarrow>
          gbij\<^bsub>((G/H)/(carrier ((Gp G N)/H))),(G/N)\<^esub> ((Qm\<^bsub>G H,N\<^esub>)\<dieresis>\<^bsub>(G/H),(G/N)\<^esub>)"
apply (frule QmpTr [of "H" "N"], assumption+)
apply (simp add:gbijec_def)
apply (rule conjI)
apply (frule Group_Qg[of "H"], frule Group_Qg[of "N"])
apply (frule inducedHom [of "G/H" "G/N" " Qmp G H N"], assumption+)
(** show  surj_to **)
apply (frule Qmpgsurjec [of "H" "N"], assumption+)
apply (frule inducedhomgsurjec [of "G/H" "G/N" "Qm\<^bsub>G H,N\<^esub>"], assumption+)
apply (simp add:gkerQmp [of "H" "N"])

(** show ginj **)
apply (frule QmpTr [of "H" "N"], assumption+)
apply (frule Group_Qg[of "H"], frule Group_Qg[of "N"])
apply (frule induced_ghom_ginjec [of "G/H" "G/N" "Qmp G H N"], assumption+)
apply (simp add:gkerQmp [of "H" "N"])
done

section "Isomorphims"

theorem (in Group) isom2:"\<lbrakk>G \<triangleright> H; G \<triangleright> N; H \<subseteq> N\<rbrakk> \<Longrightarrow>
               ((G/H)/(carrier ((Gp G N)/H))) \<cong>  (G/N)"
apply (frule homom2 [of "H" "N"], assumption+)
 apply (simp add:isomorphic_def)
 apply blast
done

theorem homom3:"\<lbrakk> Group F; Group G; G \<triangleright> N; gsurj\<^bsub>F,G\<^esub> f; 
         N1 = (iim F G f) N \<rbrakk> \<Longrightarrow> (F / N1) \<cong> (G / N)" 
apply (frule Group.Pj_gsurjec [of "G" "N"], assumption+)
apply (frule Group.Group_Qg[of "G" "N"], assumption)
apply (frule gHom_comp_gsurjec [of "F" "G" "G / N" "f" "Pj G N"], assumption+)
apply (frule inducedhomgsurjec [of "F" "G / N" "(Pj G N) \<circ>\<^bsub>F\<^esub> f"], assumption+)
apply (frule induced_ghom_ginjec [of "F" "G / N" "(Pj G N) \<circ>\<^bsub>F\<^esub> f"], assumption+) 
 apply (simp add:gsurjec_def [of "F" "G / N" "(Pj G N) \<circ>\<^bsub>F\<^esub> f"])
 apply (simp add:kern_comp_gHom[of "F" "G" "f" "N"])
 apply (frule sym, thin_tac "N1 = iim F G f N", simp)
apply (simp add:isomorphic_def gbijec_def, blast) 
done

lemma (in Group) homom3Tr1:"\<lbrakk>G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow> H \<inter> N =  
gker\<^bsub>(Gp G H),((Gp G (H \<diamondop>\<^bsub>G\<^esub> N))/N)\<^esub> 
               ((Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N) \<circ>\<^bsub>(Gp G H)\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>))"  
apply (simp add:gkernel_def, frule nsg_sg,
       simp add:Gp_carrier[of "H"],
       frule smult_sg_nsg, assumption+,
       frule Gp_smult_nsg[of "H" "N"], assumption,
       frule Group_Gp [of "H \<diamondop>\<^bsub>G\<^esub> N"])
 apply (simp add:Group.Qg_one[of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"],
        simp add:iota_def Gp_carrier, simp add:cmpghom_def compose_def,
        simp add:Gp_carrier) 
apply (rule equalityI)
apply (rule subsetI, simp, erule conjE)
 apply (frule_tac h = x in sg_subset_elem[of "H"], assumption+,
        subst Group.Pj_mem, assumption+,
        simp add:Gp_carrier,
        frule l_sub_smult[of "H" "N"], assumption+,
        rule_tac c = x in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+)
  apply (frule r_sub_smult[of "H" "N"], assumption+,
         frule_tac c = x in subsetD[of "N" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+,
         simp add:Gp_rcs[of "N" "H \<diamondop>\<^bsub>G\<^esub> N"])
  apply (simp add:rcs_fixed2)

apply (rule subsetI, simp, erule conjE, simp)
 apply (frule_tac h = x in sg_subset_elem[of "H"], assumption+)
 apply (frule l_sub_smult[of "H" "N"], assumption+,
        frule r_sub_smult[of "H" "N"], assumption+)
 apply (frule_tac x = x in Group.Pj_mem[of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"], assumption+)
       apply (simp add:Gp_carrier)
       apply (
        rule_tac c = x in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+)
 apply (frule_tac c = x in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+)
 apply (simp only:Group.Gp_rcs)
 apply (simp only:Gp_rcs[of "N" "H \<diamondop>\<^bsub>G\<^esub> N"])
 apply (frule_tac a = x in a_in_rcs[of "N"], assumption+, simp)
done     

subsection "An automorphism groups"

definition
  automg :: "_  \<Rightarrow> 
      \<lparr> carrier :: ('a \<Rightarrow> 'a) set, top :: ['a \<Rightarrow> 'a,'a \<Rightarrow> 'a] \<Rightarrow> ('a \<Rightarrow> 'a),
        iop :: ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a), one :: ('a \<Rightarrow> 'a)\<rparr>" where
  "automg G =  \<lparr> carrier = {f. gbij\<^bsub>G,G\<^esub> f}, 
        top = \<lambda>g\<in>{f. gbij\<^bsub>G,G\<^esub> f}. \<lambda>f\<in>{f. gbij\<^bsub>G,G\<^esub> f}. ( g \<circ>\<^bsub>G\<^esub> f), 
        iop = \<lambda>f\<in>{f. gbij\<^bsub>G,G\<^esub> f}. (Ifn G G f), one = I\<^bsub>G\<^esub> \<rparr>" 

lemma automgroupTr1:"\<lbrakk>Group G; gbij\<^bsub>G,G\<^esub> f; gbij\<^bsub>G,G\<^esub> g; gbij\<^bsub>G,G\<^esub> h\<rbrakk> \<Longrightarrow>
                        (h \<circ>\<^bsub>G\<^esub> g) \<circ>\<^bsub>G\<^esub> f =  h \<circ>\<^bsub>G\<^esub> (g \<circ>\<^bsub>G\<^esub> f)" 
apply (simp add:cmpghom_def, 
       unfold gbijec_def)
 apply (frule conjunct1, rotate_tac 2, frule conjunct1,
        rotate_tac 1, frule conjunct1, fold gbijec_def)
 apply (simp add:gsurjec_def, (erule conjE)+,
        frule gHom_func[of "G" "G" "f"], assumption+,
        frule gHom_func[of "G" "G" "g"], assumption+,
        frule gHom_func[of "G" "G" "h"], assumption+)
apply (simp add:compose_assoc)
done

lemma automgroup:"Group G  \<Longrightarrow> Group (automg G)"
apply (unfold Group_def [of "automg G"])
apply(auto simp: automg_def Pi_def gbij_comp_bij automgroupTr1 IdTr2 Id_l_unit l_inv_gHom inv_gbijec_gbijec)
done

subsection "Complete system of representatives"

definition
  gcsrp :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "gcsrp G H S == \<exists>f. (bij_to f (set_rcs G H) S)"
(** G_csrp is defined iff H is a nsg **)

definition
  gcsrp_map::"_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "gcsrp_map G H == \<lambda>X\<in>(set_rcs G H). SOME x. x \<in> X"

lemma (in Group) gcsrp_func:"G \<guillemotright> H \<Longrightarrow> gcsrp_map G H \<in> set_rcs G H \<rightarrow> UNIV"
by (simp add:set_rcs_def)

lemma (in Group) gcsrp_func1:"G \<guillemotright> H \<Longrightarrow> 
       gcsrp_map G H \<in> set_rcs G H \<rightarrow> (gcsrp_map G H) ` (set_rcs G H)"
by (simp add:set_rcs_def)

lemma (in Group) gcsrp_map_bij:"G \<guillemotright> H \<Longrightarrow>
         bij_to (gcsrp_map G H) (set_rcs G H) ((gcsrp_map G H) `(set_rcs G H))"
apply (simp add:bij_to_def, rule conjI)
 apply (rule surj_to_test)
 apply (rule Pi_I)
 apply (simp add:image_def, blast)
apply (rule ballI, simp add:image_def, erule bexE, simp, blast)

apply (simp add:inj_on_def)
 apply ((rule ballI)+, rule impI)
 apply (simp add:gcsrp_map_def)
 apply (frule_tac X = x in rcs_nonempty, assumption+,
        frule_tac X = y in rcs_nonempty, assumption+)
 apply (frule_tac A = x in nonempty_some, 
        frule_tac A = y in nonempty_some, simp)
apply (rule_tac X = x and Y = y in rcs_meet[of "H"], assumption+)
apply blast
done

lemma (in Group) image_gcsrp:"G \<guillemotright> H \<Longrightarrow> 
                   gcsrp G H ((gcsrp_map G H) `(set_rcs G H))"
apply (simp add:gcsrp_def)
apply (frule gcsrp_map_bij[of "H"], blast)
done

lemma (in Group) gcsrp_exists:"G \<guillemotright> H \<Longrightarrow> \<exists>S. gcsrp G H S"
by (frule image_gcsrp[of "H"], blast)

definition
 gcsrp_top :: "[_ , 'a set] \<Rightarrow>  'a \<Rightarrow>  'a  \<Rightarrow> 'a" where
 "gcsrp_top G H == \<lambda>x \<in> ((gcsrp_map G H) `(set_rcs G H)).
                     \<lambda>y \<in> ((gcsrp_map G H) `(set_rcs G H)).
 gcsrp_map G H 
  (c_top G H  
  ((invfun (set_rcs G H) ((gcsrp_map G H) `(set_rcs G H)) (gcsrp_map G H)) x) 
  ((invfun (set_rcs G H) ((gcsrp_map G H) `(set_rcs G H)) (gcsrp_map G H)) y))"

definition
  gcsrp_iop::"[_ , 'a set] \<Rightarrow> 'a \<Rightarrow> 'a" where
  "gcsrp_iop G H = (\<lambda>x \<in> ((gcsrp_map G H) `(set_rcs G H)).
    gcsrp_map G H 
    (c_iop G H
    ((invfun (set_rcs G H) ((gcsrp_map G H) `(set_rcs G H)) (gcsrp_map G H)) x)))"

definition
  gcsrp_one::"[_ , 'a set] \<Rightarrow> 'a" where
  "gcsrp_one G H = gcsrp_map G H H"

definition
  Gcsrp :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a Group" where
  "Gcsrp G N = \<lparr>carrier = (gcsrp_map G N) `(set_rcs G N),
                top = gcsrp_top G N, iop = gcsrp_iop G N, one = gcsrp_one G N\<rparr>"

lemma (in Group) gcsrp_top_closed:"\<lbrakk>Group G; G \<triangleright> N;
  a \<in> ((gcsrp_map G N) `(set_rcs G N)); b \<in> ((gcsrp_map G N) `(set_rcs G N))\<rbrakk>
 \<Longrightarrow> gcsrp_top G N a b \<in> (gcsrp_map G N) `(set_rcs G N)"
apply (frule nsg_sg[of "N"],
       frule gcsrp_func1[of "N"],
       frule gcsrp_map_bij[of "N"]) 
apply (frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "a"], assumption+,
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "b"], assumption+)
apply (frule Qg_top_closed[of "N" "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) a"
       "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) b"], assumption+)
apply (simp add:gcsrp_top_def)
done

lemma (in Group) gcsrp_tassoc:"\<lbrakk>Group G; G \<triangleright> N;
       a \<in> ((gcsrp_map G N) `(set_rcs G N)); 
        b \<in> ((gcsrp_map G N) `(set_rcs G N));
         c \<in> ((gcsrp_map G N) `(set_rcs G N))\<rbrakk> \<Longrightarrow>
      (gcsrp_top G N (gcsrp_top G N a b) c) =
               (gcsrp_top G N a (gcsrp_top G N b c))"
apply (frule nsg_sg[of "N"],
       frule gcsrp_func1[of "N"],
       frule gcsrp_map_bij[of "N"]) 
apply (frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "a"], assumption+,
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "b"], assumption+,
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "c"], assumption+)
apply (frule Qg_top_closed[of "N" "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) a"
       "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) b"], assumption+,
       frule Qg_top_closed[of "N" "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) b"
       "invfun (set_rcs G N) 
             (gcsrp_map G N ` set_rcs G N) (gcsrp_map G N) c"], assumption+) 
apply (simp add:gcsrp_top_def)
 apply (simp add:invfun_l1)
 apply (simp add:Qg_tassoc[of "N"])
done

lemma (in Group) gcsrp_l_one:"\<lbrakk>Group G; G \<triangleright> N;
       a \<in> ((gcsrp_map G N) `(set_rcs G N))\<rbrakk> \<Longrightarrow>
             (gcsrp_top G N (gcsrp_one G N) a) = a"
apply (frule nsg_sg[of "N"],
       frule gcsrp_func1[of "N"],
       frule gcsrp_map_bij[of "N"],
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "a"], assumption+)
apply (simp add:gcsrp_top_def gcsrp_one_def)
 apply (frule Qg_unit_closed[of "N"])
 apply (simp add:Pi_def invfun_l1 Qg_unit invfun_r1)
done

lemma (in Group) gcsrp_l_i:"\<lbrakk>G \<triangleright> N; a \<in> ((gcsrp_map G N) `(set_rcs G N))\<rbrakk> \<Longrightarrow>
       gcsrp_top G N (gcsrp_iop G N a) a = gcsrp_one G N"
apply (frule nsg_sg[of "N"],
       frule gcsrp_func1[of "N"],
       frule gcsrp_map_bij[of "N"],
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "a"], assumption+)
apply (frule Qg_iop_closed[of "N" "invfun (set_rcs G N) (gcsrp_map G N ` 
                       set_rcs G N) (gcsrp_map G N) a"], assumption+) 
apply (simp add:gcsrp_top_def gcsrp_one_def gcsrp_iop_def)
 apply (simp add:invfun_l1 Qg_i)
done

lemma (in Group) gcsrp_i_closed:"\<lbrakk>G \<triangleright> N; a \<in> ((gcsrp_map G N) `(set_rcs G N))\<rbrakk>
      \<Longrightarrow> gcsrp_iop G N a \<in> ((gcsrp_map G N) `(set_rcs G N))"
apply (frule nsg_sg[of "N"],
       frule gcsrp_func1[of "N"],
       frule gcsrp_map_bij[of "N"],
       frule invfun_mem1[of "gcsrp_map G N" "set_rcs G N"
          "(gcsrp_map G N) ` (set_rcs G N)" "a"], assumption+)
apply (frule Qg_iop_closed[of "N" "invfun (set_rcs G N) (gcsrp_map G N ` 
                       set_rcs G N) (gcsrp_map G N) a"], assumption+)  
apply (simp add:gcsrp_iop_def)
done

lemma (in Group) Group_Gcsrp:"G \<triangleright> N \<Longrightarrow> Group (Gcsrp G N)"
apply (simp add:Group_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Gcsrp_def)
 apply (rule Pi_I)
 apply (rule_tac a = x and b = xa in gcsrp_top_closed[of "N"], rule Group_axioms, assumption+)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:Gcsrp_def)
 apply (rule_tac a = a and b = b and c = c in gcsrp_tassoc[of "N"], rule Group_axioms, assumption+)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Gcsrp_def, rule gcsrp_i_closed[of "N"], assumption+)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (simp add:Gcsrp_def,
        rule  gcsrp_l_i[of "N"], assumption+)
apply (rule conjI)
 apply (frule Qg_unit_closed[of "N"],
        simp add:Gcsrp_def gcsrp_one_def)
apply (rule allI, rule impI)
 apply (simp add:Gcsrp_def)
 apply (rule gcsrp_l_one[of "N"], rule Group_axioms, assumption+)
done

lemma (in Group) gcsrp_map_gbijec:"G \<triangleright> N \<Longrightarrow> 
                  gbij\<^bsub>(G/N), (Gcsrp G N)\<^esub> (gcsrp_map G N)"
apply (simp add:gbijec_def gsurjec_def ginjec_def Qg_carrier Gcsrp_def) 
apply (frule nsg_sg[of "N"],
       frule gcsrp_map_bij[of "N"], simp add:bij_to_def)
apply (fold Gcsrp_def)
apply (simp add:gHom_def)

apply (rule conjI)
 apply (simp add:Qg_carrier gcsrp_map_def)
apply (rule conjI)
 apply (simp add:Qg_carrier Gcsrp_def) 
apply (fold bij_to_def)
apply (rule ballI)+
apply (simp add:Qg_def Gcsrp_def gcsrp_top_def)
apply (frule gcsrp_func1[of "N"])
apply (simp add:invfun_l1[of "gcsrp_map G N" "set_rcs G N" 
                                 "gcsrp_map G N ` set_rcs G N"])
done

lemma (in Group) Qg_equiv_Gcsrp:"G \<triangleright> N \<Longrightarrow> (G / N) \<cong> Gcsrp G N"
apply (simp add:isomorphic_def)
apply (frule gcsrp_map_gbijec[of "N"], blast)
done
 
section "Zassenhaus"

text\<open>we show \<open>H \<rightarrow> H N/N\<close> is gsurjective\<close>

lemma (in Group) homom4Tr1:"\<lbrakk>G \<triangleright> N; G \<guillemotright> H\<rbrakk> \<Longrightarrow>  Group ((Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) / N)" 
apply (frule Gp_smult_sg_nsg[of "H" "N"], assumption+)
apply (frule Gp_smult_nsg [of "H" "N"], assumption+)
 apply (simp add:Group.Group_Qg)
done

lemma homom3Tr2:"\<lbrakk>Group G; G \<guillemotright> H; G \<triangleright> N\<rbrakk> \<Longrightarrow>  
 gsurj\<^bsub>(Gp G H),((Gp G (H \<diamondop>\<^bsub>G\<^esub> N))/N)\<^esub> 
                      ((Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N) \<circ>\<^bsub>(Gp G H)\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>))"
 apply (frule iotahom[of "G" "H" "N"], assumption+,
        frule Group.Gp_smult_nsg[of "G" "H" "N"], assumption+,
        frule Group.smult_sg_nsg[of "G" "H" "N"], assumption+,
        frule Group.Gp_smult_sg_nsg[of "G" "H" "N"], assumption+,
        frule Group.Pj_gsurjec [of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"], assumption,
        frule Group.Group_Gp[of "G" "H"], assumption+,
        frule Group.Group_Qg[of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"], assumption+,
        frule gHomcomp[of "Gp G H" "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "(Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) / N" 
        "\<iota>\<^bsub>(\<natural>\<^bsub>G\<^esub>H)\<^esub>" "Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N"], assumption+) 
  apply (simp add:gsurjec_def)
 apply (subst gsurjec_def, simp)

 apply (rule surj_to_test,
        simp add:gHom_def)

 apply (rule ballI)
 apply (simp add:Group.Qg_carrier[of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"],
        simp add:set_rcs_def, erule bexE,
        frule Group.nsg_sg[of "G" "N"], assumption,
        frule Group.r_sub_smult[of "G" "H" "N"], assumption+,
        simp add:Group.Gp_carrier)
 apply (simp add:Group.Gp_rcs[of "G" "N" "H \<diamondop>\<^bsub>G\<^esub> N"])
 
 apply (thin_tac "\<iota>\<^bsub>(\<natural>\<^bsub>G\<^esub>H)\<^esub> \<in> gHom (\<natural>\<^bsub>G\<^esub>H) (\<natural>\<^bsub>G\<^esub>(H \<diamondop>\<^bsub>G\<^esub> N))",
        thin_tac "gsurj\<^bsub>(Gp G (H \<diamondop>\<^bsub>G\<^esub> N)),((\<natural>\<^bsub>G\<^esub>(H \<diamondop>\<^bsub>G\<^esub> N)) / N)\<^esub> Pj (\<natural>\<^bsub>G\<^esub>(H \<diamondop>\<^bsub>G\<^esub> N)) N",
        thin_tac "Pj (\<natural>\<^bsub>G\<^esub>(H \<diamondop>\<^bsub>G\<^esub> N)) N \<circ>\<^bsub>(\<natural>\<^bsub>G\<^esub>H)\<^esub> \<iota>\<^bsub>(\<natural>\<^bsub>G\<^esub>H)\<^esub> \<in> gHom (\<natural>\<^bsub>G\<^esub>H) ((\<natural>\<^bsub>G\<^esub>(H \<diamondop>\<^bsub>G\<^esub> N)) / N)")
 apply (simp add:cmpghom_def compose_def,
        simp add:Group.Gp_carrier iota_def,
        frule Group.smult_commute_sg_nsg[of "G" "H" "N"], assumption+,
        frule_tac a = a in eq_set_inc[of _ "H \<diamondop>\<^bsub>G\<^esub> N" "N \<diamondop>\<^bsub>G\<^esub> H"], assumption+,
        thin_tac "H \<diamondop>\<^bsub>G\<^esub> N = N \<diamondop>\<^bsub>G\<^esub> H")
 apply (simp add:s_top_def[of "G" "N" "H"], (erule bexE)+,
       rotate_tac -1, frule sym, thin_tac "x \<cdot>\<^bsub>G\<^esub> y = a", 
       frule_tac h = y in Group.sg_subset_elem[of "G" "H"], assumption+,
       simp add:Group.rcs_fixed1[THEN sym])
 apply (frule Group.l_sub_smult[of "G" "H" "N"], assumption+,
        frule_tac x1 = y in Group.Pj_mem[THEN sym, of "Gp G (H \<diamondop>\<^bsub>G\<^esub> N)" "N"],
        assumption+, simp add:Group.Gp_carrier, simp add: subsetD)
apply (frule_tac c = y in subsetD[of "H" "H \<diamondop>\<^bsub>G\<^esub> N"], assumption+,
       simp add:Group.Gp_rcs[of "G" "N" "H \<diamondop>\<^bsub>G\<^esub> N"], blast)
done


theorem homom4:"\<lbrakk>Group G; G \<triangleright> N; G \<guillemotright> H\<rbrakk> \<Longrightarrow>gbij\<^bsub>((Gp G H)/(H \<inter> N)),((Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) / N)\<^esub> (((Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N) \<circ>\<^bsub>(Gp G H)\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>))\<dieresis>\<^bsub>(Gp G H),((Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) / N)\<^esub>)"
            
apply (frule homom3Tr2 [of "G" "H" "N"], assumption+)
apply (frule Group.Gp_smult_sg_nsg, assumption+)
apply (frule Group.homom4Tr1[of "G" "N" "H"], assumption+)
apply (frule Group.Group_Gp [of "G" "H"], assumption+)
apply (frule induced_ghom_ginjec [of "Gp G H" "(Gp G (H \<diamondop>\<^bsub>G\<^esub> N)/N)" "(Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N) \<circ>\<^bsub>(Gp G H)\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>)"], assumption+) 
 apply (simp add:gsurjec_def)
apply (frule inducedhomgsurjec [of "Gp G H" "(Gp G (H \<diamondop>\<^bsub>G\<^esub> N))/N" "(Pj (Gp G (H \<diamondop>\<^bsub>G\<^esub> N)) N) \<circ>\<^bsub>(Gp G H)\<^esub> (\<iota>\<^bsub>(Gp G H)\<^esub>)"], assumption+)
 apply (frule Group.homom3Tr1[of "G" "H" "N"], assumption+)
 apply simp
apply (simp add:gbijec_def)   
done

lemma (in Group) homom4_2:"\<lbrakk>G \<triangleright> N; G \<guillemotright> H\<rbrakk> \<Longrightarrow> Group ((Gp G H) / (H \<inter> N))" 
by (frule Group_Gp[of "H"],
    frule inter_Gp_nsg[of "N" "H"], assumption,
    rule Group.Group_Qg, assumption+)

lemma isom4:"\<lbrakk>Group G; G \<triangleright> N; G \<guillemotright> H\<rbrakk> \<Longrightarrow>
                 ((Gp G H)/(H \<inter> N)) \<cong>  ((Gp G (N \<diamondop>\<^bsub>G\<^esub> H)) / N)"
apply (frule homom4 [of "G" "N" "H"], assumption+,
       frule Group.smult_sg_nsg[of "G" "H" "N"], assumption+,
       frule Group.smult_commute_sg_nsg[of "G" "H" "N"], assumption+)
 apply (simp add:isomorphic_def, blast)
done

lemma ZassenhausTr5:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
      Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow>
   ((Gp G (H \<inter> K))/((H1 \<inter> K) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1))) \<cong> 
                          ((Gp G (H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)))/(H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1)))"
apply (frule Group.ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+,
       frule Group.Group_Gp [of "G" "H1 \<diamondop>\<^bsub>G\<^esub> (H \<inter> K)"], assumption+,
       frule Group.ZassenhausTr3 [of "G" "H" "H1" "K" "K1"], assumption+,
       frule Group.inter_sgs [of "G" "H" "K"], assumption+,
       frule Group.r_sub_smult[of "G" "H1" "H \<inter> K"], assumption+,
       frule Group.sg_sg[of "G" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K" "H \<inter> K"], assumption+,
       frule isom4 [of "Gp G (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K)" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1" "H \<inter> K"], 
                                                             assumption+)
apply (simp add:Int_commute[of "H \<inter> K" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1"])
apply (frule Group.Group_Gp[of "G" "H"], assumption,
       frule Group.Group_Gp[of "G" "K"], assumption,
       frule Group.nsg_sg[of "Gp G H" "H1"], assumption+,
       frule Group.sg_subset[of "Gp G H" "H1"], assumption+,
       frule Group.nsg_sg[of "Gp G K" "K1"], assumption+, 
       frule Group.sg_subset[of "Gp G K" "K1"], assumption+, 
       simp add:Group.Gp_carrier,
       frule Group.inter_sgs[of "G" "H" "K1"], assumption+,
       cut_tac subset_self[of "H"],
       frule Int_mono[of "H" "H" "K1" "K"], assumption)
apply (simp add:Group.s_topTr6_1[of "G" "H1" "H \<inter> K1" "H \<inter> K"],
       simp add:Int_assoc[THEN sym, of "H1" "H" "K"]) 
  
apply (simp add:Int_absorb2[of "H1" "H"],
       simp add:Group.Gp_inherited[of "G" "H \<inter> K" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"])
 apply (frule Group.s_top_mono[of "G" "H1" "H \<inter> K" "H1" "H \<inter> K1"],
        frule Group.sg_subset[of "G" "H"], assumption+,
        rule subset_trans[of "H1" "H" "carrier G"], assumption+)
  apply (rule Group.sg_subset[of "G" "H \<inter> K"], assumption+, simp,
         simp,
         (frule Group.ZassenhausTr2_1[of "G" "H" "H1" "K"], assumption+,
          frule Group.subg_sg_sg[of "G" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1"],
                                  assumption+, simp add:Group.nsg_sg))
  apply (simp add:Group.s_top_induced[of "G" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1" "H \<inter> K"],
         simp add:Group.s_top_assoc[of "G" "H1" "H \<inter> K1" "H \<inter> K"],
         cut_tac subset_self[of "H"],
         frule Int_mono[of "H" "H" "K1" "K"], assumption)
  apply (simp add:Group.K_absorb_HK[of "G" "H \<inter> K1" "H \<inter> K"])
  apply (cut_tac subset_self[of "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"],
         simp add:Group.Gp_inherited[of "G" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"])
done

lemma ZassenhausTr5_1:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow>   ((Gp G (K \<inter> H))/((K1 \<inter> H) \<diamondop>\<^bsub>G\<^esub> (K \<inter> H1))) \<cong> 
                          ((Gp G (K1 \<diamondop>\<^bsub>G\<^esub> (K \<inter> H)))/(K1 \<diamondop>\<^bsub>G\<^esub> (K \<inter> H1)))"
(* thm ZassenhausTr5 [of "G" "K" "K1" "H" "H1"] *)
apply (simp add:ZassenhausTr5 [of "G" "K" "K1" "H" "H1"]) 
done

lemma ZassenhausTr5_2: "\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow>
      ((Gp G (H \<inter> K))/((H1 \<inter> K) \<diamondop>\<^bsub>G\<^esub> (H \<inter> K1))) = 
                       ((Gp G (K \<inter> H))/((K1 \<inter> H) \<diamondop>\<^bsub>G\<^esub> (K \<inter> H1)))"
by (simp add:Group.ZassenhausTr3_3[of "G" "H" "H1" "K" "K1"],
       simp add:Int_commute[of "H" "K"])

lemma ZassenhausTr6_1:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> Group  (Gp G (H \<inter> K) / (H1 \<inter> K \<diamondop>\<^bsub>G\<^esub> H \<inter> K1))"
apply (frule Group.inter_sgs [of "G" "H" "K"], assumption+,
       frule Group.Group_Gp [of "G" "H \<inter> K"], assumption+,
       frule Group.ZassenhausTr3_5 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (rule Group.Group_Qg, assumption+)
done

lemma ZassenhausTr6_2:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> Group (Gp G (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K) / (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1))"
apply (frule Group.ZassenhausTr2_1 [of "G" "H" "H1" "K"], assumption+,
       frule Group.Group_Gp [of "G" "H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K"], assumption+,
       frule Group.ZassenhausTr3 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (simp add:Group.Group_Qg)
done

lemma ZassenhausTr6_3:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> Group (Gp G (K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H) / (K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H1))"
apply (frule Group.ZassenhausTr2_1 [of "G" "K" "K1" "H"], assumption+,
       frule Group.Group_Gp [of "G" "K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H"], assumption+,
       frule Group.ZassenhausTr3[of "G" "K" "K1" "H" "H1"], assumption+)
apply (simp add:Group.Group_Qg)
done

theorem Zassenhaus:"\<lbrakk>Group G; G \<guillemotright> H; G \<guillemotright> H1; G \<guillemotright> K; G \<guillemotright> K1; Gp G H \<triangleright> H1; 
       Gp G K \<triangleright> K1\<rbrakk> \<Longrightarrow> (Gp G (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K) / (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1)) \<cong> 
                              (Gp G (K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H) / (K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H1))" 
apply (frule ZassenhausTr6_1[of "G" "K" "K1" "H" "H1"], assumption+)
apply (frule ZassenhausTr6_3 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (frule ZassenhausTr6_2 [of "G" "H" "H1" "K" "K1"], assumption+)
apply (rule isomTr2[of "(\<natural>\<^bsub>G\<^esub>(H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K)) / (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1)" 
             "(\<natural>\<^bsub>G\<^esub>(K \<inter> H)) / (K1 \<inter> H \<diamondop>\<^bsub>G\<^esub> K \<inter> H1)"
             "(\<natural>\<^bsub>G\<^esub>(K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H)) / (K1 \<diamondop>\<^bsub>G\<^esub> K \<inter> H1)"], assumption+)
apply (frule ZassenhausTr5_1[of "G" "K" "K1" "H" "H1"], assumption+)
apply (simp add:Int_commute[of "K" "H"])
apply (simp add:Group.ZassenhausTr3_3[THEN sym, of "G" "H" "H1" "K" "K1"])
apply (rule isomTr1[of  "(\<natural>\<^bsub>G\<^esub>(H \<inter> K)) / (H1 \<inter> K \<diamondop>\<^bsub>G\<^esub> H \<inter> K1)" 
                        "(\<natural>\<^bsub>G\<^esub>(H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K)) / (H1 \<diamondop>\<^bsub>G\<^esub> H \<inter> K1)"], assumption+)
apply (rule ZassenhausTr5_1[of "G" "H" "H1" "K" "K1"], assumption+)
done


section "Chain of groups I"  

definition
  d_gchain :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "d_gchain G n g = (if n=0 then G \<guillemotright> g 0 else (\<forall>l\<le> n. G \<guillemotright> (g l) \<and> 
            (\<forall>l \<le> (n - Suc 0). g (Suc l) \<subseteq> g l )))" 
            (**  g 0 \<supseteq> \<dots> \<supseteq> g n  **)

definition
  D_gchain :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "D_gchain G n g = (if n = 0 then G \<guillemotright> (g 0) else (d_gchain G n g) \<and> 
      (\<forall>l \<le> (n - Suc 0). (g (Suc l)) \<subset> (g l)))"
            (**  g 0 \<supset> \<dots> \<supset> g n **) 

definition
  td_gchain :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "td_gchain G n g = (if n=0 then g 0 = carrier G \<and> g 0 = {\<one>\<^bsub>G\<^esub>} else 
       d_gchain G n g \<and> g 0 = carrier G \<and> g n = {\<one>\<^bsub>G\<^esub>})"
           (**  g 0 \<supseteq> \<dots> \<supseteq> g n with g 0 = carrier G and g n = {e}  **)

definition
  tD_gchain :: "[_, nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "tD_gchain G n g = (if n=0 then g 0 = carrier G \<and> g 0 = {\<one>\<^bsub>G\<^esub>} else 
        D_gchain G n g \<and> (g 0 = carrier G) \<and> (g n = {\<one>\<^bsub>G\<^esub>}))" 
           (**  g 0 \<supset> \<dots> \<supset> g n with g 0 = carrier G and g n = {e}  **)

definition
  w_cmpser :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "w_cmpser G n g = (if n = 0 then d_gchain G n g else d_gchain G n g \<and>  
    (\<forall>l \<le> (n - 1). (Gp G (g l)) \<triangleright> (g (Suc l))))" 
           (**  g 0 \<rhd> \<dots> \<rhd> g n ** with g l \<supseteq> g (Suc l) **) 

definition
  W_cmpser :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "W_cmpser G n g = (if n = 0 then d_gchain G 0 g else D_gchain G n g \<and> 
    (\<forall>l \<le> (n - 1). (Gp G (g l)) \<triangleright> (g (Suc l))))" 
           (**  g 0 \<rhd> \<dots> \<rhd> g n  with g i \<supset> g (Suc i) **) 

definition
  tw_cmpser :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "tw_cmpser G n g = (if n = 0 then td_gchain G 0 g else td_gchain G n g \<and> 
    (\<forall>l \<le> (n - 1). (Gp G (g l)) \<triangleright> (g (Suc l))))" 
         (**  g 0 \<rhd> \<dots> \<rhd> g n with g 0 = carrier G and g n = {e}  **) 

definition
  tW_cmpser :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> bool" where
  "tW_cmpser G n g = (if n = 0 then td_gchain G 0 g else tD_gchain G n g \<and> 
     (\<forall>l \<le> (n - 1). (Gp G (g l)) \<triangleright> (g (Suc l))))"
    (* g 0 \<rhd> \<dots> \<rhd> g n with g 0 = carrier G, g n = {e} and g (Suc i) \<subset> g i*) 

definition
  Qw_cmpser :: "[_ , nat \<Rightarrow> 'a set] \<Rightarrow> (nat \<Rightarrow> ('a set) Group)" where
  "Qw_cmpser G f l = ((Gp G (f l)) / (f (Suc l)))" 

 (* f 0 \<rhd> \<dots> \<rhd> f (n+1), Qw_cmpser G n f is (f 0)/(f 1),\<dots>,f n/f (n+1) *)

definition
  red_chn :: "[_ , nat, (nat \<Rightarrow> 'a set)] \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "red_chn G n f = (SOME g. g \<in> {h.(tW_cmpser G (card (f ` {i. i \<le> n}) - 1) h)
    \<and> h `{i. i \<le> (card (f ` {i. i \<le> n}) - 1)} = f `{i. i \<le> n}})"

definition
  chain_cutout :: "[nat, (nat \<Rightarrow> 'a set) ] \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "chain_cutout l f = (\<lambda>j. f (slide l j))"

lemma (in Group) d_gchainTr0:"\<lbrakk>0 < n; d_gchain G n f; k \<le> (n - 1)\<rbrakk>
                        \<Longrightarrow> f (Suc k) \<subseteq> f k"
apply (simp add:d_gchain_def) 
apply (frule_tac a = k in forall_spec)
 apply (rule Nat.le_trans, assumption+, simp)
 apply (erule conjE, rotate_tac 2,
       frule_tac a = k in forall_spec, assumption, 
       thin_tac "\<forall>l\<le>n - Suc 0. f (Suc l) \<subseteq> f l",
       thin_tac "\<forall>l\<le>n. G \<guillemotright> f l  \<and> (\<forall>l\<le>n - Suc 0. f (Suc l) \<subseteq> f l)")
 apply assumption
done

lemma (in Group) d_gchain_mem_sg:"d_gchain G n f \<Longrightarrow> \<forall>i\<le> n. G \<guillemotright> (f i)"
apply (rule allI)
apply (rule impI, simp add:d_gchain_def)
apply (case_tac "n = 0", simp)
apply simp
done

lemma (in Group) d_gchain_pre:"d_gchain G (Suc n) f \<Longrightarrow> d_gchain G n f"
apply (simp add:d_gchain_def, rule impI, rule impI)
apply (rule allI, rule impI)
apply (frule_tac a = l in forall_spec, arith)
apply (erule conjE)
apply (thin_tac "\<forall>l\<le>Suc n. G \<guillemotright> f l  \<and> (\<forall>l\<le>n. f (Suc l) \<subseteq> f l)",
       frule_tac a = l in forall_spec, arith, assumption) 
done

lemma (in Group) d_gchainTr1:"0 < n \<longrightarrow> (\<forall>f. d_gchain G n f \<longrightarrow> 
                     (\<forall>l \<le> n. \<forall>j \<le> n. l < j \<longrightarrow> f j \<subseteq> f l))"
apply (induct_tac n)
 apply (rule impI, simp) 
(** n **)
apply (rule impI, rule allI, rule impI)
apply ((rule allI, rule impI)+, rule impI)
(** case n = 0 **)
apply (case_tac "n = 0", simp)
 apply (case_tac "j = 0", simp, 
        frule le_imp_less_or_eq, thin_tac "j \<le> Suc 0",
        simp, simp add:d_gchain_def)
 apply (frule_tac a = 0 in forall_spec, simp, simp)

(** case 0 < n **) 
 apply simp
 (** case j = n **)
apply (case_tac "j = Suc n")
 apply (frule d_gchain_pre, 
        frule_tac a = f in forall_spec, assumption,
        thin_tac "\<forall>f. d_gchain G n f \<longrightarrow> (\<forall>l\<le>n. \<forall>j\<le>n. l < j \<longrightarrow> f j \<subseteq> f l)",
        thin_tac "d_gchain G n f",
        simp add:d_gchain_def)
 apply (frule_tac a = n in forall_spec, simp,
        thin_tac "\<forall>l\<le>Suc n. G \<guillemotright> f l  \<and> (\<forall>l\<le>n. f (Suc l) \<subseteq> f l)",
        erule conjE,
        rotate_tac -1,
        frule_tac a = n in forall_spec, simp,
        thin_tac "\<forall>l\<le>n. f (Suc l) \<subseteq> f l",
        frule_tac x = l and n = n in Suc_less_le)
  apply (case_tac "l = n", simp,
         thin_tac "l < Suc n",
         frule_tac x = l and y = n in le_imp_less_or_eq, 
         thin_tac "l \<le> n", simp)
  apply (frule_tac a = l in forall_spec, simp,
         thin_tac "\<forall>l\<le>n. \<forall>j\<le>n. l < j \<longrightarrow> f j \<subseteq> f l") apply (
         frule_tac a = n in forall_spec) apply (simp,
         thin_tac "\<forall>j\<le>n. l < j \<longrightarrow> f j \<subseteq> f l", simp)
  apply (simp add: d_gchain_pre)
done

lemma (in Group) d_gchainTr2:"\<lbrakk>0 < n; d_gchain G n f; l \<le> n; j \<le> n; l \<le> j \<rbrakk>
                               \<Longrightarrow> f j \<subseteq> f l"
apply (case_tac "l = j", simp)
apply (metis Group.d_gchainTr1 [OF Group_axioms] antisym_conv2)
done

lemma (in Group) im_d_gchainTr1:"\<lbrakk>d_gchain G n f;
       f l \<in> (f ` {i. i \<le> n}) - {f 0}\<rbrakk> \<Longrightarrow> 
    f (LEAST j. f j \<in> (f ` {i. i \<le> n}) - {f 0}) \<in> (f ` {i. i \<le> n} - {f 0})"
apply (rule LeastI)
apply simp
done

lemma (in Group) im_d_gchainTr1_0:"\<lbrakk>d_gchain G n f; 
                 f l \<in> (f ` {i. i \<le> n}) - {f 0}\<rbrakk>  \<Longrightarrow> 
                 0 < (LEAST j. f j \<in> (f ` {i. i \<le> n}) - {f 0})"
apply (frule im_d_gchainTr1 [of "n" "f"], assumption+)
apply (rule contrapos_pp, simp)
apply simp
done 

lemma (in Group) im_d_gchainTr1_1:
      "\<lbrakk>d_gchain G n f; \<exists> i. f i \<in> (f ` {i. i \<le> n}) - {f 0}\<rbrakk>  \<Longrightarrow>
  f (LEAST j. f j \<in> ((f ` {i. i \<le> n}) - {f 0})) \<in> ((f` {i. i \<le> n}) - {f 0})"
apply (subgoal_tac "\<forall>i. f i \<in> f ` {i. i \<le> n} - {f 0} \<longrightarrow> 
        f (LEAST j. f j \<in> f `{i. i \<le> n} - {f 0}) \<in> f ` {i. i\<le> n} - {f 0}")
apply blast
 apply (thin_tac "\<exists>i. f i \<in> f `{i. i \<le> n} - {f 0}")
 apply (rule allI) apply (rule impI)
apply (rule im_d_gchainTr1 [of "n" "f" _], assumption+)
done

lemma (in Group) im_d_gchainsTr1_2:"
      \<lbrakk>d_gchain G n f; i \<le> n; f i \<in> f `{i. i \<le> n} - {f 0}\<rbrakk>  \<Longrightarrow>
          (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) \<le> i"
by (rule Least_le, assumption)

lemma (in Group) im_d_gchainsTr1_3:"\<lbrakk>d_gchain G n f; \<exists>i \<le> n. 
                 f i \<in> f` {i. i \<le> n} - {f 0};
                 k < (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0}))\<rbrakk> \<Longrightarrow> f k = f 0"
apply (erule exE)
apply (rule contrapos_pp, simp+)
apply (frule_tac i = i in im_d_gchainsTr1_2 [of "n" "f" _ ], simp+)  
apply (erule conjE)+ 
apply (frule_tac x = k and 
                 y = "LEAST j. f j \<in> f ` {i. i \<le> n} \<and> f j \<noteq> f 0" and
                 z = i in less_le_trans, assumption,
       frule_tac x = k and 
                 y = i and
                 z = n in less_le_trans, assumption)
apply (frule_tac i = k in im_d_gchainsTr1_2 [of "n" "f" _ ], simp+)  
done
 
lemma (in Group) im_gdchainsTr1_4:"\<lbrakk>d_gchain G n f;
       \<exists>v\<in>f `{i. i \<le> n}. v \<notin> {f 0}; i < (LEAST j. f j \<in> (f `{i. i \<le> n}) \<and> 
       f j \<noteq> f 0) \<rbrakk> \<Longrightarrow> f i = f 0"
apply (rule im_d_gchainsTr1_3 [of "n" "f" "i"], assumption,
       thin_tac "i < (LEAST j. f j \<in> f ` {i. i \<le> n} \<and> f j \<noteq> f 0)",
       simp add:image_def, blast)
apply simp
done

lemma (in Group) im_d_gchainsTr1_5:"\<lbrakk>0 < n; d_gchain G n f; i \<le> n; 
f i \<in> (f ` {i. i \<le> n} - {f 0}); (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) = j\<rbrakk> 
\<Longrightarrow>         f `{i. i \<le> (j - (Suc 0))} = {f 0}"
apply (frule im_d_gchainTr1_0 [of "n" "f" "i"], assumption+)
apply (subst image_def)
apply (rule equalityI)
apply (rule subsetI, simp, erule exE, erule conjE)
 apply (frule_tac x = xa and y = "j - Suc 0" and 
        z = "(LEAST j. f j \<in> f ` {i. i \<le> n} \<and> f j \<noteq> f 0)" in le_less_trans,
        simp,
        frule_tac k = xa in im_d_gchainsTr1_3[of "n" "f"])
  apply (simp, blast, simp, simp) 
apply (rule subsetI, blast)
done

lemma (in Group) im_d_gchains1:"\<lbrakk>0 < n; d_gchain G n f; i \<le> n; 
                 f i \<in> (f ` {i. i \<le> n} - {f 0}); 
                 (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) = j \<rbrakk> \<Longrightarrow> 
                         f `{i. i \<le> n} = {f 0} \<union> {f i |i. j \<le> i \<and> i \<le> n}"
apply (frule im_d_gchainTr1_0 [of "n" "f" "i"], assumption+,
       frule im_d_gchainsTr1_2 [of "n" "f" "i"], assumption+,
       frule Nset_nset_1 [of "n" "j - Suc 0"])
apply simp
apply (subst im_set_un2, simp)
apply (subst im_d_gchainsTr1_5[of "n" "f" "i" "j"]) 
apply (simp, assumption, simp+)

apply (rule equalityI)
 apply (rule subsetI, simp, erule disjE, simp,
        simp add:image_def nset_def, erule exE, blast) 
 apply (rule subsetI)
 apply (simp, erule disjE, simp)
 apply (erule exE, simp add:nset_def)
done

lemma (in Group) im_d_gchains1_1:"\<lbrakk>d_gchain G n f; f n \<noteq> f 0\<rbrakk>  \<Longrightarrow> 
      f `{i. i \<le> n} = {f 0} \<union> 
         {f i |i. (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) \<le> i \<and> i \<le> n}"
  apply (case_tac "n = 0")
   apply simp
  apply simp
  apply (frule im_d_gchains1 [of "n" "f" "n" 
                "(LEAST j. f j \<in> f ` {i. i \<le> n} - {f 0})"], assumption+,
       simp add:n_in_Nsetn)
    apply (cut_tac n_in_Nsetn[of "n"], simp,
       simp)
  apply (simp cong del: image_cong)
  done

lemma (in Group) d_gchains_leastTr:"\<lbrakk>d_gchain G n f; f n \<noteq> f 0\<rbrakk>  \<Longrightarrow>  
               (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) \<in> {i. i \<le> n} \<and> 
               f  (LEAST j. f j \<in> (f `{i. i \<le> n} - {f 0})) \<noteq> f 0"
apply (frule im_d_gchainsTr1_2 [of "n" "f" "n"],
       simp add:n_in_Nsetn,
       simp add:image_def, blast,
       frule mem_of_Nset[of "LEAST j. f j \<in> f ` {i. i \<le> n} - {f 0}" "n"],
       simp)
apply (frule im_d_gchainTr1[of "n" "f" "n"],
       simp add:image_def, cut_tac n_in_Nsetn[of "n"], blast)
apply (simp add:image_def)
done

lemma (in Group) im_d_gchainTr2:"\<lbrakk>d_gchain G n f; j \<le> n; f j \<noteq> f 0\<rbrakk> \<Longrightarrow>
                                 \<forall>i \<le> n. f 0 = f i \<longrightarrow> \<not> j \<le> i"
apply (case_tac "n = 0", simp, simp)
apply (rule allI, rule impI)
apply (rule contrapos_pp, simp+)
apply (case_tac "j = i", simp) 
apply (frule d_gchainTr2 [of "n" "f" "0" "j"], assumption+,
       simp, (erule conjE)+,
       rule_tac i = j and j = i and k = n in le_trans, assumption+,
       simp,
       (erule conjE)+,
       frule_tac l = j and j = i in d_gchainTr2 [of "n" "f"], assumption+)

       apply simp+
done

lemma (in Group) D_gchain_pre:"\<lbrakk>D_gchain G (Suc n) f\<rbrakk> \<Longrightarrow> D_gchain G n f"
apply (simp add:D_gchain_def, erule conjE)
apply (case_tac "n = 0", rotate_tac -1)
 apply (simp, insert lessI [of "0::nat"], simp)
 apply (simp add:d_gchain_def, simp)
 apply (frule d_gchain_pre [of "n"])
 apply simp 
done

lemma (in Group) D_gchain0:"\<lbrakk>D_gchain G n f; i \<le> n; j \<le> n; i < j\<rbrakk> \<Longrightarrow>
                             f j \<subset> f i" 
apply (case_tac "n = 0") 
 apply (simp, simp)
apply (cut_tac d_gchainTr1[of "n"], simp)
 apply (simp add:D_gchain_def, frule conjunct1)
 apply (frule_tac a = f in forall_spec, assumption,
        thin_tac "\<forall>f. d_gchain G n f \<longrightarrow> (\<forall>l\<le>n. \<forall>j\<le>n. l < j \<longrightarrow> f j \<subseteq> f l)") 
 apply (frule_tac a = i in forall_spec,
        frule_tac x = i and y = j and z = n in less_le_trans, assumption+,
        simp)
apply ( thin_tac "\<forall>l\<le>n. \<forall>j\<le>n. l < j \<longrightarrow> f j \<subseteq> f l",
        frule_tac a = j in forall_spec, assumption, 
        thin_tac "\<forall>j\<le>n. i < j \<longrightarrow> f j \<subseteq> f i", simp) 
apply (frule Suc_leI[of i j],
       frule less_le_trans[of i j n], assumption+,
       frule less_le_diff[of i n])
apply (frule_tac a = i in forall_spec, assumption,
       thin_tac "\<forall>l\<le>n - Suc 0. f (Suc l) \<subset> f l")
 apply (cut_tac d_gchainTr2[of "n" "f" "Suc i" "j"])
 apply blast apply simp+
done

lemma (in Group) D_gchain1:"D_gchain G n f \<Longrightarrow> inj_on f {i. i \<le> n}"
apply (case_tac "n = 0")
 apply (simp add:inj_on_def)
apply (simp) (** case 0 < n **)
apply (simp add:inj_on_def)
 apply ((rule allI)+, rule impI, rule contrapos_pp, simp+, erule exE)
 apply (cut_tac x = x and y = y in less_linear, simp)
apply (erule disjE, (erule conjE)+)
 apply (frule_tac i = x and j = y in D_gchain0 [of "n" "f"], assumption+,
        simp,
        simp, frule_tac i = y and j = x in D_gchain0 [of "n" "f"],
        simp+)
done

lemma (in Group) card_im_D_gchain:"\<lbrakk>0 < n; D_gchain G n f\<rbrakk> 
                                   \<Longrightarrow> card (f `{i. i \<le> n}) = Suc n"
apply (frule D_gchain1 [of "n"])
apply (subst card_image, assumption+, simp)
done

lemma (in Group) w_cmpser_gr:"\<lbrakk>0 < r; w_cmpser G r f; i \<le> r\<rbrakk>
                             \<Longrightarrow> G \<guillemotright>  (f i)"
by (simp add:w_cmpser_def, erule conjE, simp add:d_gchain_def)

lemma (in Group) w_cmpser_ns:"\<lbrakk>0 < r; w_cmpser G r f; i \<le> (r - 1)\<rbrakk> \<Longrightarrow>
                                 (Gp G (f i)) \<triangleright> (f (Suc i))"
apply (simp add:w_cmpser_def)
done

lemma (in Group) w_cmpser_pre:"w_cmpser G (Suc n) f \<Longrightarrow> w_cmpser G n f"
apply (simp add:w_cmpser_def)
 apply (erule conjE)
 apply (case_tac "n = 0", rotate_tac -1, simp)
 apply (rule d_gchain_pre [of "0" "f"], assumption+)
apply simp
 apply (frule d_gchain_pre [of "n" "f"])
 apply simp
done

lemma (in Group) W_cmpser_pre:"W_cmpser G (Suc n) f \<Longrightarrow> W_cmpser G n f"
apply (simp add:W_cmpser_def)
 apply (erule conjE)
 apply (case_tac "n = 0", simp,
        simp add:D_gchain_def, erule conjE,
        rule d_gchain_pre, assumption+, simp)

apply (frule D_gchain_pre, simp)
done

lemma (in Group) td_gchain_n:"\<lbrakk>td_gchain G n f; carrier G \<noteq> {\<one>}\<rbrakk> \<Longrightarrow> 0 < n"
apply (simp add:td_gchain_def)
apply (rule contrapos_pp, simp+) 
apply (erule conjE, simp) 
done

section "Existence of reduced chain" 

lemma (in Group) D_gchain_is_d_gchain:"D_gchain G n f \<Longrightarrow> d_gchain G n f"
apply (simp add:D_gchain_def)
 apply (case_tac "n = 0") apply (rotate_tac -1) 
 apply (simp add:d_gchain_def) apply (rotate_tac -1)
 apply simp
done

lemma (in Group) joint_d_gchains:"\<lbrakk>d_gchain G n f; d_gchain G m g; 
  g 0 \<subseteq> f n \<rbrakk> \<Longrightarrow>  d_gchain G (Suc (n + m)) (jointfun n f m g)" 
apply (case_tac "n = 0")
 apply (case_tac "m = 0")
 apply (simp add:d_gchain_def [of "G" "Suc (n + m)" _])
 apply (simp add:jointfun_def sliden_def d_gchain_def)
 apply (simp add:jointfun_def sliden_def d_gchain_def)
 apply (rule allI) apply (rule conjI) apply (rule impI) 
 apply (rule allI) apply (rule impI)+ apply simp 
 apply (frule_tac a = la in forall_spec, assumption,
        thin_tac "\<forall>l\<le>m. G \<guillemotright> g l  \<and> (\<forall>l\<le>m - Suc 0. g (Suc l) \<subseteq> g l)",
        erule conjE)
 apply (frule_tac a = "la - Suc 0" in forall_spec,
        thin_tac "\<forall>l\<le>m - Suc 0. g (Suc l) \<subseteq> g l",
        rule diff_le_mono, assumption, simp)
 apply (rule impI, rule impI) 
 apply (frule_tac m = l and n = "Suc m" and l = "Suc 0" in diff_le_mono)
       apply simp
       apply (rule allI, rule impI, rule impI) 
       apply (frule_tac a = la in forall_spec,assumption,
              thin_tac "\<forall>l\<le>m. G \<guillemotright> g l  \<and> (\<forall>l\<le>m - Suc 0. g (Suc l) \<subseteq> g l)",
              erule conjE)
        apply (frule_tac a = "la - Suc 0" in forall_spec, simp) 
apply simp_all
 apply (simp add:d_gchain_def [of "G" _ "jointfun n f m g"])
 apply (rule allI, rule impI) apply (rule conjI)
 apply (case_tac "l \<le> n", simp add:jointfun_def d_gchain_def[of _ n f])
 apply (simp add:jointfun_def sliden_def,
        frule_tac m = l and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
        thin_tac "l \<le> Suc (n + m)", simp add:d_gchain_def[of _ m g])
 apply (case_tac "m = 0", simp, simp)

apply (rule allI, rule impI)
 apply (case_tac "Suc la \<le> n")
 apply (simp add:jointfun_def)
 apply (rule_tac l = la and j = "Suc la" in d_gchainTr2[of n f],
        simp+)
 apply (simp add:jointfun_def)
 apply (cut_tac y = "Suc la" and x = n in not_less [symmetric], simp)
 apply (frule_tac m = n and n = "Suc la" in Suc_leI,
        thin_tac "n < Suc la", simp)
 apply (case_tac "la = n", simp add:sliden_def)
apply (frule not_sym, thin_tac "la \<noteq> n", 
       frule_tac x = n and y = la in le_imp_less_or_eq, 
       thin_tac "n \<le> la", simp,
       frule_tac m = n and n = la in Suc_leI, simp add:sliden_def)
 apply (simp add:d_gchain_def[of _ m g])
 apply (cut_tac m = la and n = "n + m" and l = "Suc n" in diff_le_mono,
         assumption, simp)
 apply (frule_tac a = m in forall_spec, simp,
        thin_tac "\<forall>l\<le>m. G \<guillemotright> g l  \<and> (\<forall>l\<le>m - Suc 0. g (Suc l) \<subseteq> g l)",
        erule conjE) apply (
        frule_tac a = "la - Suc n" in forall_spec, assumption,
        thin_tac "\<forall>l\<le>m - Suc 0. g (Suc l) \<subseteq> g l")
 apply (cut_tac n1 = n and i1 = la  in jointgd_tool4[THEN sym], simp+)
done
 
lemma (in Group) joint_D_gchains:"\<lbrakk>D_gchain G n f; D_gchain G m g; 
       g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  D_gchain G (Suc (n + m)) (jointfun n f m g)" 
apply (simp add:D_gchain_def [of "G" "Suc (n + m)" _])
apply (rule conjI)
apply (rule joint_d_gchains[of n f m g],
       simp add:D_gchain_is_d_gchain,
       simp add:D_gchain_is_d_gchain,
       simp add:psubset_imp_subset)
apply (rule allI, rule impI)
 apply (case_tac "Suc l \<le> n")
 apply (simp add:jointfun_def)
 apply (rule_tac i = l and j = "Suc l" in D_gchain0[of n f], assumption,
        cut_tac x = l and y = "Suc l" and z = n in less_le_trans) 
        apply simp+
 apply (simp add:nat_not_le_less,
        frule_tac m = n and n = "Suc l" in Suc_leI, thin_tac "n < Suc l", simp)
 apply (case_tac "l = n", simp add:jointfun_def sliden_def)
 apply (frule not_sym, thin_tac "l \<noteq> n",
        frule_tac x = n and y = l in le_imp_less_or_eq,
        thin_tac "n \<le> l", simp)
 apply (simp add:jointfun_def sliden_def)
 apply (frule_tac m = l and n = "n + m" and l = n in  diff_le_mono)
        apply (simp add:diff_add_assoc)
 apply (rule_tac i = "l - Suc n" and j = "l - n" in D_gchain0[of m g],
         assumption) 
 apply (arith, assumption, arith)
done
  
lemma (in Group) w_cmpser_is_d_gchain:"w_cmpser G n f \<Longrightarrow> d_gchain G n f"
apply (simp add:w_cmpser_def)
 apply (case_tac "n=0") apply (rotate_tac -1) apply simp
 apply (rotate_tac -1) apply simp
done

lemma (in Group) joint_w_cmpser:"\<lbrakk>w_cmpser G n f; w_cmpser G m g; 
 Gp G (f n) \<triangleright> (g 0)\<rbrakk> \<Longrightarrow> w_cmpser G (Suc (n + m)) (jointfun n f m g)"
apply (simp add:w_cmpser_def [of _ "Suc (n + m)" _])
apply (rule conjI)
 apply (frule w_cmpser_is_d_gchain[of "n" "f"],
        frule w_cmpser_is_d_gchain[of "m" "g"])
  apply (rule joint_d_gchains, assumption+) 
  apply (frule d_gchain_mem_sg[of "n" "f"],
         cut_tac n_in_Nsetn[of "n"],
         frule_tac a = n in forall_spec, simp,
         thin_tac "\<forall>i \<le> n. G \<guillemotright> f i")
  apply (frule Group_Gp[of "f n"],
         frule Group.nsg_sg[of "Gp G (f n)" "g 0"], assumption,
         frule Group.sg_subset[of "Gp G (f n)" "g 0"], assumption,
         simp add:Gp_carrier)
apply (rule allI, rule impI)
 apply (case_tac "n = 0") apply simp
 apply (simp add:jointfun_def)
  apply (case_tac "l = 0")
  apply simp apply (simp add:sliden_def)
 apply simp
 apply (simp add:w_cmpser_def [of _ "m" "g"])
 apply (case_tac "m = 0") apply (simp add:sliden_def)
 apply (erule conjE)
 apply (simp add:sliden_def)
 apply (frule_tac x = 0 and y = l and z = m in less_le_trans, assumption+) 
 apply (frule_tac m = l and n = m and l = "Suc 0" in diff_le_mono)
 apply (frule_tac a = "l - Suc 0" in forall_spec, assumption,
        thin_tac "\<forall>l\<le>(m - Suc 0). (\<natural>(g l)) \<triangleright> (g (Suc l))")
 apply simp
 apply (case_tac "l \<le> n - Suc 0", simp) 
 apply (frule less_pre_n [of "n"])
 apply (frule_tac x = l in le_less_trans[of _ "n - Suc 0" "n"], assumption+) 
 apply (simp add:jointfun_def w_cmpser_def [of _ "n"])
apply (simp add:nat_not_le_less)
 apply (frule_tac n = l in Suc_leI [of "n - Suc 0" _], simp)
 apply (case_tac "n = l")
 apply (frule sym) apply (thin_tac "n = l")
 apply simp
 apply (simp add:jointfun_def sliden_def)
 apply (frule_tac m = n and n = l in noteq_le_less, assumption+)
 apply (frule_tac m = n and n = l in Suc_leI)
 apply (simp add:jointfun_def)
 apply (frule_tac m = l and n = "n + m" and l = "Suc n" in diff_le_mono)
 apply simp
 apply (simp add:sliden_def w_cmpser_def [of _ "m" _])
 apply (erule conjE)
 apply (simp add:jointgd_tool4)
done  

lemma (in Group) W_cmpser_is_D_gchain:"W_cmpser G n f \<Longrightarrow> D_gchain G n f"
apply (simp add:W_cmpser_def)
 apply (case_tac "n = 0") apply (rotate_tac -1) apply simp
 apply (simp add:D_gchain_def d_gchain_def)
 apply (rotate_tac -1) apply simp
done

lemma (in Group) W_cmpser_is_w_cmpser:"W_cmpser G n f \<Longrightarrow> w_cmpser G n f"
apply (simp add:W_cmpser_def)
apply (case_tac "n = 0") apply (rotate_tac -1)
 apply simp
 apply (simp add:w_cmpser_def)
 apply (rotate_tac -1)
apply simp apply (erule conjE)
 apply (frule D_gchain_is_d_gchain)
 apply (simp add:w_cmpser_def)
done

lemma (in Group) tw_cmpser_is_w_cmpser:"tw_cmpser G n f \<Longrightarrow> w_cmpser G n f"
apply (simp add:tw_cmpser_def)
 apply (case_tac "n = 0")
 apply (rotate_tac -1) apply simp
 apply (simp add:td_gchain_def w_cmpser_def) 
 apply (simp add:d_gchain_def) apply (simp add:special_sg_G)
apply (rotate_tac -1) apply simp
 apply (erule conjE) apply (simp add:td_gchain_def)
 apply (erule conjE)+
apply (simp add:w_cmpser_def)
done

lemma (in Group) tW_cmpser_is_W_cmpser:"tW_cmpser G n f \<Longrightarrow> W_cmpser G n f"
apply (simp add:tW_cmpser_def)
apply (case_tac "n = 0") apply (rotate_tac -1)
 apply simp
 apply (simp add:td_gchain_def)
 apply (simp add:W_cmpser_def d_gchain_def) apply (simp add:special_sg_G)
apply (rotate_tac -1) apply simp
apply (erule conjE)
 apply (simp add:tD_gchain_def)
 apply (erule conjE)+
 apply (simp add:W_cmpser_def)
done

lemma (in Group) joint_W_cmpser:"\<lbrakk>W_cmpser G n f; W_cmpser G m g; 
      (Gp G (f n)) \<triangleright> (g 0); g 0 \<subset> f n\<rbrakk> \<Longrightarrow> 
      W_cmpser G (Suc (n + m)) (jointfun n f m g)"
apply (simp add:W_cmpser_def [of _ "Suc (n + m)" _])
 apply (frule W_cmpser_is_D_gchain [of "n" "f"],
        frule W_cmpser_is_D_gchain [of "m" "g"])
 apply (simp add:joint_D_gchains)
apply (frule W_cmpser_is_w_cmpser [of "n" _],
       frule W_cmpser_is_w_cmpser [of "m" _])
 apply (frule joint_w_cmpser [of "n" "f" "m" "g"], assumption+)
 apply (simp add:w_cmpser_def [of _ "Suc (n + m)" _])
done

lemma (in Group) joint_d_gchain_n0:"\<lbrakk>d_gchain G n f; d_gchain G 0 g;
       g 0 \<subseteq> f n \<rbrakk> \<Longrightarrow>  d_gchain G (Suc n) (jointfun n f 0 g)"
apply (frule joint_d_gchains [of "n" "f" "0" "g"], assumption+)
apply simp
done

lemma (in Group) joint_D_gchain_n0:"\<lbrakk>D_gchain G n f; D_gchain G 0 g; 
       g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  D_gchain G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_D_gchains [of "n" "f" "0" "g"], assumption+)
apply simp
done

lemma (in Group) joint_w_cmpser_n0:"\<lbrakk>w_cmpser G n f; w_cmpser G 0 g; 
      (Gp G (f n)) \<triangleright> (g 0)\<rbrakk> \<Longrightarrow>  w_cmpser G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_w_cmpser [of "n" "f" "0" "g"], assumption+)
apply simp
done

lemma (in Group) joint_W_cmpser_n0:"\<lbrakk>W_cmpser G n f; W_cmpser G 0 g; 
      (Gp G (f n)) \<triangleright> (g 0); g 0 \<subset> f n \<rbrakk> \<Longrightarrow>  
                       W_cmpser G (Suc n) (jointfun n f 0 g)" 
apply (frule joint_W_cmpser [of "n" "f" "0" "g"], assumption+)
apply simp
done

definition
  simple_Group :: "_ \<Rightarrow> bool" where
  "simple_Group G \<longleftrightarrow> {N. G \<guillemotright> N} = {carrier G, {\<one>\<^bsub>G\<^esub>}}"

definition
  compseries:: "[_ , nat, nat \<Rightarrow> 'a set] \<Rightarrow> bool" where
  "compseries G n f \<longleftrightarrow> tW_cmpser G n f \<and> (if n = 0 then f 0 = {\<one>\<^bsub>G\<^esub>} else 
    (\<forall>i \<le> (n - 1). (simple_Group ((Gp G (f i))/(f (Suc i))))))"

definition
  length_twcmpser :: "[_ , nat, nat \<Rightarrow> 'a set] \<Rightarrow> nat" where
  "length_twcmpser G n f = card (f `{i. i \<le> n}) - Suc 0" 


lemma (in Group) compseriesTr0:"\<lbrakk>compseries G n f; i \<le> n\<rbrakk> \<Longrightarrow>
                                    G \<guillemotright> (f i)"
apply (simp add:compseries_def) 
 apply (frule conjunct1)
 apply (fold compseries_def)
 apply (frule tW_cmpser_is_W_cmpser,
        frule W_cmpser_is_w_cmpser, 
        frule w_cmpser_is_d_gchain)
apply (frule d_gchain_mem_sg[of "n" "f"])
 apply simp
done

lemma (in Group) compseriesTr1:"compseries G n f \<Longrightarrow> tW_cmpser G n f"
apply (simp add:compseries_def)
done

lemma (in Group) compseriesTr2:"compseries G n f \<Longrightarrow> f 0 = carrier G"
apply (frule compseriesTr1, simp add:tW_cmpser_def)
apply (case_tac "n = 0")
 apply (simp add:td_gchain_def)
apply simp
apply (erule conjE, simp add:tD_gchain_def)
done

lemma (in Group) compseriesTr3:"compseries G n f \<Longrightarrow> f n = {\<one>}"
apply (frule compseriesTr1)
apply (simp add:tW_cmpser_def)
apply (case_tac "n = 0")
apply (simp add:td_gchain_def)
apply (auto del:equalityI)
apply (simp add:tD_gchain_def)
done

lemma (in Group) compseriesTr4:"compseries G n f \<Longrightarrow> w_cmpser G n f"
apply (frule compseriesTr1,
       frule tW_cmpser_is_W_cmpser)
apply (rule W_cmpser_is_w_cmpser, assumption)
done

lemma (in Group) im_jointfun1Tr1:"\<forall>l \<le> n. G \<guillemotright> (f l) \<Longrightarrow>
                               f \<in> {i. i \<le> n} \<rightarrow> Collect (sg G)"
apply (simp add:Pi_def)
done

lemma (in Group) Nset_Suc_im:"\<forall>l \<le> (Suc n). G \<guillemotright> (f l) \<Longrightarrow>
                 insert (f (Suc n)) (f ` {i. i \<le> n}) = f ` {i. i \<le> (Suc n)}"
apply (rule equalityI)
 apply (rule subsetI)
  apply (simp add:image_def)
  apply (erule disjE) apply blast
  apply (erule exE, erule conjE)
  apply (frule_tac x = xa and y = n and z = "Suc n" in le_less_trans,
         simp,
         frule_tac x = xa and y = "Suc n" in less_imp_le, blast)
 apply (cut_tac Nset_Suc [of "n"], simp)
done

definition
  NfuncPair_neq_at::"[nat \<Rightarrow> 'a set, nat \<Rightarrow> 'a set, nat] \<Rightarrow> bool" where
  "NfuncPair_neq_at f g i \<longleftrightarrow> f i \<noteq> g i" 

lemma LeastTr0:"\<lbrakk> (i::nat) < (LEAST l. P (l))\<rbrakk> \<Longrightarrow> \<not> P (i)"
apply (rule not_less_Least)
apply simp
done

lemma (in Group) funeq_LeastTr1:"\<lbrakk>\<forall>l\<le> n. G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
  (l :: nat) < (LEAST k. (NfuncPair_neq_at f g k)) \<rbrakk> \<Longrightarrow> f l = g l"
apply (rule contrapos_pp, simp+)
apply (frule  LeastTr0 [of "l" "NfuncPair_neq_at f g"])
apply (simp add:NfuncPair_neq_at_def)
done

lemma (in Group) funeq_LeastTr1_1:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright>  g l; 
  (l :: nat) < (LEAST k. (f k \<noteq>  g k)) \<rbrakk> \<Longrightarrow> f l = g l"
apply (rule funeq_LeastTr1[of "n" "f" "g" "l"], assumption+)
apply (simp add:NfuncPair_neq_at_def)
done

lemma (in Group) Nfunc_LeastTr2_1:"\<lbrakk>i \<le> n; \<forall>l \<le> n. G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l;
       NfuncPair_neq_at f g i\<rbrakk> \<Longrightarrow> 
        NfuncPair_neq_at f g (LEAST k. (NfuncPair_neq_at f g k))" 
apply (simp add: LeastI [of "NfuncPair_neq_at f g" "i"])
done

lemma (in Group) Nfunc_LeastTr2_2:"\<lbrakk>i \<le> n; \<forall>l \<le> n. G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l;
        NfuncPair_neq_at f g i\<rbrakk> \<Longrightarrow> 
                          (LEAST k. (NfuncPair_neq_at f g k)) \<le> i" 
apply (simp add: Least_le [of "NfuncPair_neq_at f g" "i"])
done

lemma (in Group) Nfunc_LeastTr2_2_1:"\<lbrakk>i \<le> (n::nat); \<forall>l \<le> n. G \<guillemotright> f l;
       \<forall>l \<le> n. G \<guillemotright> g l; f i \<noteq> g i\<rbrakk> \<Longrightarrow> (LEAST k. (f k \<noteq> g k)) \<le> i"
apply (rule contrapos_pp, simp+)
apply (simp add:nat_not_le_less)
apply (frule Nfunc_LeastTr2_2 [of "i" "n" "f" "g"], assumption+)
apply (simp add:NfuncPair_neq_at_def)+
done

lemma (in Group) Nfunc_LeastTr2_3:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
      i \<le> n; f i \<noteq> g i\<rbrakk>  \<Longrightarrow>  
      f (LEAST k. (f k \<noteq>  g k)) \<noteq> g (LEAST k. (f k \<noteq>  g k))" 
apply (frule  Nfunc_LeastTr2_1 [of "i" "n" "f" "g"], assumption+)
apply (simp add:NfuncPair_neq_at_def)+
done

lemma  (in Group) Nfunc_LeastTr2_4:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
      i \<le> n; f i \<noteq> g i\<rbrakk> \<Longrightarrow>(LEAST k. (f k \<noteq> g k)) \<le> n" 
apply (frule_tac i = i in Nfunc_LeastTr2_2 [of  _ "n" "f" "g"], 
                                      assumption+)
apply (simp add:NfuncPair_neq_at_def)
apply (frule le_trans [of "(LEAST k. NfuncPair_neq_at f g k)" "i" "n"],
                                  assumption+)
apply (simp add:NfuncPair_neq_at_def)
done

lemma (in Group) Nfunc_LeastTr2_5:"\<lbrakk>\<forall>l\<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
      \<exists>i \<le> n. (f i \<noteq> g i)\<rbrakk>  \<Longrightarrow>  
      f (LEAST k. (f k \<noteq> g k)) \<noteq> g ((LEAST k. f k \<noteq> g k))"
apply (erule exE)
apply (rule_tac i = i in Nfunc_LeastTr2_3[of n f g], assumption+, simp+)
done

lemma (in Group) Nfunc_LeastTr2_6:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l;
       \<exists>i \<le> n. (f i \<noteq> g i)\<rbrakk> \<Longrightarrow> (LEAST k. (f k \<noteq> g k)) \<le> n"
apply (erule exE)
apply (rule_tac i = i in  Nfunc_LeastTr2_4, assumption+, simp+)
done

lemma (in Group) Nfunc_Least_sym:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
     \<exists>i \<le> n. (f i \<noteq> g i)\<rbrakk> \<Longrightarrow> 
           (LEAST k. (f k \<noteq> g k)) = (LEAST k. (g k \<noteq> f k))"
apply (erule exE)
 apply (frule_tac i = i in Nfunc_LeastTr2_4 [of n f g], assumption+,
        simp+,
        frule_tac i = i in Nfunc_LeastTr2_3 [of n f g _], assumption+,
        simp+,
        frule_tac i = i in Nfunc_LeastTr2_4 [of n g f], assumption+,
        simp+, rule not_sym, simp,
        frule_tac i = i in Nfunc_LeastTr2_3 [of n g f _], assumption+,
        simp+, rule not_sym, simp)
 apply (frule_tac i = "(LEAST k. f k \<noteq> g k)" in 
           Nfunc_LeastTr2_2_1 [of _ "n" "g" "f"], assumption+,
         rule not_sym, simp) apply (
        frule_tac i = "(LEAST k. g k \<noteq> f k)" in 
           Nfunc_LeastTr2_2_1 [of _ n f g], assumption+,
           rule not_sym, simp)  
 apply (rule le_antisym, assumption+)
done

lemma Nfunc_iNJTr:"\<lbrakk>inj_on g {i. i \<le> (n::nat)}; i \<le> n; j \<le> n; i < j \<rbrakk> \<Longrightarrow> g i \<noteq> g j"
apply (unfold inj_on_def)
apply (simp add:CollectI)
apply (rule contrapos_pp, simp+)
apply (frule_tac a = i in forall_spec) 
apply (frule_tac x = i and y = j and z = n in less_le_trans, assumption+,
       simp add:less_imp_le,
       thin_tac "\<forall>x\<le>n. \<forall>y\<le>n. g x = g y \<longrightarrow> x = y",
       rotate_tac -1,
       frule_tac a = j in forall_spec, assumption,
       thin_tac "\<forall>y\<le>n. g i = g y \<longrightarrow> i = y")
apply simp
done

lemma (in Group) Nfunc_LeastTr2_7:"\<lbrakk>\<forall>l \<le> (n::nat). G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
      inj_on g {i. i \<le> n}; \<exists>i \<le> n. (f i \<noteq> g i); 
      f k = g (LEAST k.(f k \<noteq> g k))\<rbrakk> \<Longrightarrow>(LEAST k.(f k \<noteq> g k)) < k"
apply (rule contrapos_pp, simp+) 
apply (simp add:nat_not_le_less[THEN sym, of "LEAST k. f k \<noteq> g k" "k"])
apply (frule le_imp_less_or_eq)
apply (case_tac "k = (LEAST k. f k \<noteq> g k)")
 apply simp 
 apply (frule  Nfunc_LeastTr2_5 [of "n" "f" "g"], assumption+)
 apply simp 
apply (frule funeq_LeastTr1_1 [of "n" "f" "g" "k"], assumption+)
 apply simp
apply (frule Nfunc_LeastTr2_6 [of "n" "f" "g"], assumption+)
 apply simp
 apply (frule_tac le_trans[of "k" "LEAST k. f k \<noteq> g k" "n"], assumption+)
 apply (frule mem_of_Nset[of "k" "n"])
 apply (simp add:inj_on_def[of "g"])
done

lemma (in Group) Nfunc_LeastTr2_8:"\<lbrakk>\<forall>l \<le> n. G \<guillemotright> f l; \<forall>l \<le> n. G \<guillemotright> g l; 
     inj_on g {i. i \<le> n}; \<exists>i \<le> n. f i \<noteq> g i; f `{i. i \<le> n} = g `{i. i \<le> n}\<rbrakk>
 \<Longrightarrow> 
  \<exists> k \<in>(nset (Suc (LEAST i. (f i \<noteq> g i))) n). f k = g (LEAST i. (f i \<noteq> g i))"
apply (frule_tac Nfunc_LeastTr2_6 [of "n" "f" "g"], assumption+)
apply (cut_tac mem_in_image2[of "LEAST k. f k \<noteq> g k" "{i. i \<le> n}" "g"])
 apply (frule sym, thin_tac "f ` {i. i \<le> n} = g ` {i. i \<le> n}", simp)
 apply (thin_tac "g ` {i. i \<le> n} = f ` {i. i \<le> n}")
 apply (simp add:image_def)
 apply (rotate_tac -1, erule exE)
 apply (frule_tac k = x in Nfunc_LeastTr2_7[of "n" "f" "g"], assumption+)
 apply (erule conjE) apply (rule sym, assumption)
 apply (frule_tac m = "(LEAST k. f k \<noteq> g k)" and n = x in Suc_leI)
 apply (simp add:nset_def)
apply blast apply simp
done

lemma (in Group) ex_redchainTr1:"\<lbrakk>d_gchain G n f; 
       D_gchain G (card (f ` {i. i \<le> n}) - Suc 0) g; 
       g ` {i. i \<le> (card (f ` {i. i \<le> n}) - Suc 0)} = f ` {i. i \<le> n}\<rbrakk> \<Longrightarrow> 
       g (card (f ` {i. i \<le> n}) - Suc 0) = f n" 
apply (case_tac "n = 0", simp, simp)
apply (rule contrapos_pp, simp+)
apply (cut_tac n_in_Nsetn[of "card (f ` {i. i \<le> n}) - Suc 0"])
apply (frule mem_in_image2[of "card (f ` {i. i \<le> n}) - Suc 0" 
                           "{i. i \<le> (card (f ` {i. i \<le> n}) - Suc 0)}" "g"])
 apply (cut_tac n_in_Nsetn[of "n"])
 apply (frule mem_in_image2[of "n" "{i. i \<le> n}" "f"])
 apply simp
 apply (simp add:image_def[of "f" "{i. i \<le> n}"])
 apply (erule exE)
 apply (frule_tac l = x in d_gchainTr2[of "n" "f" _ "n"], assumption+)
 apply simp+
 apply (erule conjE)
 apply (rotate_tac -1, frule sym,
        thin_tac "g (card {y. \<exists>x\<le>n. y = f x} - Suc 0) = f x",
        simp,
        thin_tac "f x = g (card {y. \<exists>x\<le>n. y = f x} - Suc 0)")
 apply (cut_tac mem_in_image2[of "n" "{i. i \<le> n}" "f"],
        unfold image_def)
 apply (frule sym,
        thin_tac "{y. \<exists>x\<in>{i. i \<le> card {y. \<exists>x\<le>n. y = f x} - Suc 0}. y = g x} =
         {y. \<exists>x\<le>n. y = f x}")
 apply (cut_tac eq_set_inc[of "f n" "{y. \<exists>x \<le> n. y = f x}"
         "{y. \<exists>x\<in>{i. i \<le> card {y. \<exists>x\<le>n. y = f x} - Suc 0}. y = g x}"]) 
 apply (thin_tac "{y. \<exists>x\<le>n. y = f x} =
         {y. \<exists>x\<in>{i. i \<le> card {y. \<exists>x\<le>n. y = f x} - Suc 0}. y = g x}",
        thin_tac "f n \<in> {y. \<exists>x\<in>{i. i \<le> n}. y = f x}")
apply  (simp, erule exE, erule conjE)
 apply (case_tac "xa \<le> card {y. \<exists>x\<le>n. y = f x} - Suc 0", simp)
 apply (frule D_gchain_is_d_gchain[of "card {y. \<exists>x\<le>n. y = f x} - Suc 0" g])
 apply (case_tac "card {y. \<exists>x \<le> n. y = f x} - Suc 0 = 0", 
         simp)
 apply (frule nat_nonzero_pos[of "card {y. \<exists>x \<le> n. y = f x} - Suc 0"],
        thin_tac "card {y. \<exists>x\<le>n. y = f x} - Suc 0 \<noteq> 0")
 apply (frule_tac l = xa in d_gchainTr2[of 
  "card {y. \<exists>x \<le> n. y = f x} - Suc 0" "g" _ 
                 "card {y. \<exists>x \<le> n. y = f x} - Suc 0"], assumption+)
 apply simp apply simp
 apply (frule_tac A = "g xa" and 
        B = "g (card {y. \<exists>x \<le> n. y = f x} - Suc 0)" in equalityI,
        assumption+, simp) apply simp+
done

lemma (in Group) ex_redchainTr1_1:"\<lbrakk>d_gchain G (n::nat) f; 
       D_gchain G (card (f ` {i. i \<le> n}) - Suc 0) g; 
       g ` {i. i \<le> (card (f ` {i. i \<le> n}) - Suc 0)} = f ` {i. i \<le> n}\<rbrakk> \<Longrightarrow>
       g 0 = f 0"
apply (cut_tac Nset_inc_0[of "n"],
        frule mem_in_image2[of "0" "{i. i \<le> n}" "f"]) apply (
        frule sym) apply ( 
       thin_tac "g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0} = f ` {i. i \<le> n}")
  apply (
       frule eq_set_inc[of "f 0" "f ` {i. i \<le> n}" 
                 "g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}"], assumption)
apply (       
 thin_tac "f 0 \<in> f ` {i. i \<le> n}",
        thin_tac "0 \<in> {i. i \<le> n}")
apply (cut_tac Nset_inc_0[of "card (f ` {i. i \<le> n}) - Suc 0"],
        frule mem_in_image2[of "0" "{i. i \<le> (card (f ` {i. i \<le> n}) - Suc 0)}"
         "g"],
        frule sym) apply (
       frule eq_set_inc[of "g 0" "g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}" 
               "f ` {i. i \<le> n}"], assumption) apply (
       thin_tac "f ` {i. i \<le> n} = g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}")
 apply (
       thin_tac "0 \<in> {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}") apply (
       thin_tac "g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0} = f ` {i. i \<le> n}")
 apply (
       thin_tac "g 0 \<in> g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}")
apply (case_tac "n = 0", simp)
 apply (simp)
 apply (cut_tac mem_in_image3[of "f 0" "g" 
                "{i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}"],
        frule mem_in_image3[of "g 0" "f" 
                    "{i. i \<le> n}"]) apply (
        thin_tac "f 0 \<in> g ` {i. i \<le> card (f ` {i. i \<le> n}) - Suc 0}",
        thin_tac "g 0 \<in> f ` {i. i \<le> n}") apply (erule bexE)+ apply (
        frule_tac j = aa in d_gchainTr2[of "n" "f" "0"], assumption+) 
  apply simp+ 
apply (rotate_tac -2, frule sym, thin_tac "g 0 = f aa", simp)
apply (case_tac "a = 0", simp)
apply (simp,
       frule_tac j = a in D_gchain0[of "card (f ` {i. i \<le> n}) - Suc 0" g 0],
       simp add:Nset_inc_0, assumption+,
       simp add:psubset_contr) 
apply simp
done

lemma (in Group) ex_redchainTr2:"d_gchain G (Suc n) f 
               \<Longrightarrow> D_gchain G 0 (constmap {0::nat} {f (Suc n)})"
apply (simp add:D_gchain_def constmap_def)
apply (simp add:d_gchain_def)
done

lemma (in Group) last_mem_excluded:"\<lbrakk>d_gchain G (Suc n) f; f n \<noteq> f (Suc n)\<rbrakk> \<Longrightarrow>
                                   f (Suc n) \<notin> f ` {i. i \<le> n}"
apply (rule contrapos_pp, simp+)
apply (frule mem_in_image3[of "f (Suc n)" "f" "{i. i \<le> n}"], erule bexE)
apply (cut_tac zero_less_Suc[of "n"]) 
apply (frule_tac l = a in d_gchainTr2[of "Suc n" "f" _ "n"], assumption+)
 apply simp+ 
 apply (frule sym, thin_tac "f (Suc n) = f a", simp) 
apply (cut_tac l = n and j = "Suc n" in  d_gchainTr2[of "Suc n" "f"])
 apply simp+
done

lemma (in Group) ex_redchainTr4:"\<lbrakk>d_gchain G (Suc n) f; f n \<noteq> f (Suc n)\<rbrakk> \<Longrightarrow>
                card (f ` {i. i \<le> (Suc n)}) = Suc (card (f ` {i. i \<le> n}))"
apply (cut_tac image_Nset_Suc [of "f" "n"])
apply simp
apply (rule card_insert_disjoint)
apply (simp)
apply (simp add:last_mem_excluded)
done

lemma (in Group) ex_redchainTr5:"d_gchain G n f \<Longrightarrow> 0 < card (f ` {i. i\<le> n})"
apply (simp add:image_Nsetn_card_pos)
done

lemma (in Group) ex_redchainTr6:"\<forall>f. d_gchain G n f \<longrightarrow> 
      (\<exists>g. D_gchain G (card (f `{i. i \<le> n}) - 1) g \<and> 
                  (g ` {i. i \<le> (card (f `{i. i \<le> n}) - 1)} = f `{i. i \<le> n}))"
apply (induct_tac n)
apply (rule allI, rule impI)
 apply (simp add:image_def)
   apply (simp add:D_gchain_def d_gchain_def)
   apply blast
(** n **)
apply (rule allI, rule impI)
apply (case_tac "f (Suc n) = f n")
 apply (cut_tac n = n in Nset_Suc)
 apply (cut_tac n = n in n_in_Nsetn,
        frule_tac a = n and A = "{i. i \<le> n}" and f = f in mem_in_image2)
 apply (frule sym) apply (thin_tac "f (Suc n) = f n", simp)
 apply (subst insert_absorb, assumption)+
 apply (frule_tac n = n and f = f in d_gchain_pre, blast)

apply (frule_tac n = n and f = f in d_gchain_pre)
 apply (frule_tac a = f in forall_spec, assumption,
        thin_tac "\<forall>f. d_gchain G n f \<longrightarrow>
               (\<exists>g. D_gchain G (card (f ` {i. i \<le> n}) - 1) g \<and>
                    g ` {i. i \<le> card (f ` {i. i \<le> n}) - 1} =
                    f ` {i. i \<le> n})")
 apply (erule exE, erule conjE)
apply (simp add:image_Nset_Suc)

apply (frule_tac n = n and f = f in ex_redchainTr2)
apply (frule_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g and 
       g = "constmap {0} {f (Suc n)}" in joint_D_gchain_n0, assumption+)
apply (simp add: ex_redchainTr1)
 apply (simp add: constmap_def Nset_inc_0) 
 apply (cut_tac n = n in zero_less_Suc) 
 apply (frule_tac n = "Suc n" and f = f and l = n and j = "Suc n" in 
        d_gchainTr2, assumption+)
        apply simp  apply simp  apply simp
 apply (simp add:psubset_eq)
 apply (cut_tac f = f and n = n in image_Nsetn_card_pos,
        cut_tac k = n in finite_Collect_le_nat, 
        frule_tac F = "{i. i \<le> n}" and h = f in finite_imageI,
        frule_tac n = n and f = f in last_mem_excluded,
        rule not_sym, assumption)
 apply simp+
 apply (cut_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g and m = 0 and 
        g = "constmap {0} {f (Suc n)}" in im_jointfun1)
 apply simp
 apply (simp add:Nset_0 constmap_def)
apply blast
done

lemma (in Group) ex_redchain:"d_gchain G n f \<Longrightarrow>
      (\<exists>g. D_gchain G (card (f ` {i. i \<le> n}) - 1) g \<and> 
       g ` {i. i \<le> (card (f ` {i. i \<le> n}) - 1)} = f ` {i. i \<le> n})"
apply (cut_tac ex_redchainTr6 [of "n"])
apply simp
done

lemma (in Group) const_W_cmpser:"d_gchain G (Suc n) f \<Longrightarrow>
                         W_cmpser G 0 (constmap {0::nat} {f (Suc n)})"
apply (simp add:W_cmpser_def d_gchain_def constmap_def)
done

lemma (in Group) ex_W_cmpserTr0m:"\<forall>f. w_cmpser G m f \<longrightarrow>  
  (\<exists>g. (W_cmpser G (card (f `{i. i \<le> m}) - 1) g \<and> 
           g `{i. i \<le> (card (f `{i. i \<le> m}) - 1)} = f `{i. i \<le> m}))"
apply (induct_tac m)
(********* induct_step m = 0 ***************)
apply (rule allI, rule impI) 
 apply simp 
 apply (simp add:w_cmpser_def W_cmpser_def)
 apply blast
(********** induct_step  m ****************)
apply (rule allI, rule impI)  
 apply (case_tac "f (Suc n) = f n")
 apply (cut_tac n = n in Nset_Suc)
 apply (cut_tac n = n in n_in_Nsetn,
        frule_tac a = n and A = "{i. i \<le> n}" and f = f in mem_in_image2)
 apply (frule sym) apply (thin_tac "f (Suc n) = f n", simp)
 apply (subst insert_absorb, assumption)+
 apply (frule_tac n = n and f = f in  w_cmpser_pre, blast)

apply (frule_tac n = n and f = f in w_cmpser_pre)
 apply (frule_tac a = f in forall_spec, assumption,
        thin_tac "\<forall>f. w_cmpser G n f \<longrightarrow>
               (\<exists>g. W_cmpser G (card (f ` {i. i \<le> n}) - 1) g \<and>
                    g ` {i. i \<le> card (f ` {i. i \<le> n}) - 1} =
                    f ` {i. i \<le> n})")
 apply (erule exE, erule conjE)
apply (simp add:image_Nset_Suc,
       frule_tac n = "Suc n" and f = f in w_cmpser_is_d_gchain,
       frule_tac n = n and f = f in const_W_cmpser)
apply (frule_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g and 
       g = "constmap {0::nat} {f (Suc n)}" in joint_W_cmpser_n0, assumption+)
 apply (frule_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g in 
                      W_cmpser_is_D_gchain)
 apply (frule d_gchain_pre)
 apply (subst ex_redchainTr1, assumption+)
 apply (simp add:constmap_def Nset_inc_0)
 apply (simp add:w_cmpser_def)
 apply (frule d_gchain_pre)
 apply (frule_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g in 
                      W_cmpser_is_D_gchain)
 apply (frule_tac n = n and f = f and g = g in ex_redchainTr1, assumption+)
        apply simp
 apply (simp add:constmap_def Nset_inc_0,
        thin_tac "d_gchain G n f", simp add:d_gchain_def) 
 apply (cut_tac n = "Suc n" in n_in_Nsetn,
        frule_tac x = "Suc n" in spec, simp,
        simp add:psubset_eq)
 apply (cut_tac f = f and n = n in image_Nsetn_card_pos,
        cut_tac k = n in finite_Collect_le_nat, 
        frule_tac F = "{i. i \<le> n}" and h = f in finite_imageI,
        frule_tac n = n and f = f in last_mem_excluded,
        rule not_sym, assumption)
 apply simp+
 apply (cut_tac n = "card (f ` {i. i \<le> n}) - Suc 0" and f = g and m = 0 and 
        g = "constmap {0::nat} {f (Suc n)}" in im_jointfun1)
 apply simp
 apply (simp add:Nset_0 constmap_def)
apply blast
done

lemma (in Group) ex_W_cmpser:"w_cmpser G m f \<Longrightarrow>
       \<exists>g. W_cmpser G (card (f ` {i. i \<le> m}) - 1) g  \<and>  
              g ` {i. i \<le> (card (f ` {i. i \<le> m}) - 1)} = f ` {i. i \<le> m}"
apply (cut_tac ex_W_cmpserTr0m [of "m"])
apply simp
done

section "Existence of reduced chain and composition series"

lemma (in Group) ex_W_cmpserTr3m1:"\<lbrakk>tw_cmpser G (m::nat) f; 
       W_cmpser G ((card (f ` {i. i \<le> m})) - 1) g; 
       g ` {i. i \<le> ((card (f ` {i. i \<le> m})) - 1)} = f `{i. i \<le> m}\<rbrakk> \<Longrightarrow> 
      tW_cmpser G ((card (f ` {i. i \<le> m})) - 1) g"
apply (frule_tac tw_cmpser_is_w_cmpser [of "m" "f"],
       frule_tac w_cmpser_is_d_gchain [of "m" "f"],
       frule_tac W_cmpser_is_D_gchain [of "(card (f ` {i. i \<le> m}) - 1)" "g"])

apply (frule ex_redchainTr1 [of "m" "f" "g"])
 apply simp+
apply (frule_tac ex_redchainTr1_1 [of "m" "f" "g"])
 apply (simp add:tW_cmpser_def tw_cmpser_def)
 apply (case_tac "m = 0") apply simp
 apply (cut_tac card_image_le [of "{0::nat}" "f"])
 apply (simp, simp)
apply (simp add:tW_cmpser_def)
 apply (case_tac "card (f ` {i. i \<le> m}) \<le> Suc 0") apply simp
 apply (simp add:td_gchain_def tw_cmpser_def) 
 apply (case_tac "m = 0") 
 apply (thin_tac "f 0 = f m", thin_tac "g 0 = f m") apply simp
 apply ( simp add:td_gchain_def) apply ( erule conjE, simp)
 apply simp
 apply (simp add:td_gchain_def[of "G" "m" "f"], (erule conjE)+, simp)
apply simp
 apply (simp add:tD_gchain_def tw_cmpser_def td_gchain_def [of _ "m" "f"])
apply (case_tac "m = 0", simp add:card1)
 apply (simp, erule conjE, simp add:td_gchain_def)
 apply (simp add:W_cmpser_def)
done

lemma (in Group) ex_W_cmpserTr3m:"tw_cmpser G m f \<Longrightarrow> 
           \<exists>g. tW_cmpser G ((card (f ` {i. i \<le> m})) - 1) g \<and> 
               g `{ i. i \<le> (card (f `{i. i \<le> m}) - 1)} = f ` {i. i \<le> m}"
apply (frule tw_cmpser_is_w_cmpser[of "m" "f"])
apply (frule ex_W_cmpser [of "m" "f"])
apply (auto del:equalityI)
apply (frule_tac g = g in ex_W_cmpserTr3m1 [of "m" "f"])
apply simp+ apply blast
done

definition
  red_ch_cd :: "[_ , nat \<Rightarrow> 'a set, nat, nat \<Rightarrow> 'a set ] \<Rightarrow> bool" where
  "red_ch_cd G f m g \<longleftrightarrow> tW_cmpser G (card (f ` {i. i \<le> m}) - 1) g \<and> 
                 (g `{i . i \<le> (card (f ` {i. i \<le> m}) - 1)} = f` {i. i \<le> m})"
 
definition
  red_chain :: "[_ , nat, nat \<Rightarrow> 'a set] \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "red_chain G m f = (SOME g. g \<in> {h. red_ch_cd G f m h})"

lemma (in Group) red_chainTr0m1_1:"tw_cmpser G m f \<Longrightarrow> 
       (SOME g. g \<in> {h. red_ch_cd G f m h}) \<in> {h. red_ch_cd G f m h}"
apply (rule nonempty_some [of "{h. red_ch_cd G f m h}"])
apply (frule ex_W_cmpserTr3m [of "m" "f"])
 apply simp
 apply (simp add:red_ch_cd_def)
done

lemma (in Group) red_chain_m:"tw_cmpser G m f \<Longrightarrow> 
      tW_cmpser G (card (f ` {i. i \<le> m}) - 1) (red_chain G m f) \<and> 
      (red_chain G m f) `{i. i \<le> (card (f `{i. i \<le> m}) - 1)} = f ` {i. i \<le> m}"
apply (frule red_chainTr0m1_1 [of "m" "f"])
apply simp
apply (simp add:red_ch_cd_def)
apply (simp add:red_chain_def)
done

section "Chain of groups II"

definition
  Gchain :: "[nat, nat \<Rightarrow> (('a set), 'more) Group_scheme] \<Rightarrow> bool" where
  "Gchain n g \<longleftrightarrow> (\<forall>l \<le> n. Group (g l))"  

definition
  isom_Gchains :: "[nat, nat \<Rightarrow> nat, nat \<Rightarrow> (('a set), 'more) Group_scheme, 
            nat \<Rightarrow> (('a set), 'more) Group_scheme]  \<Rightarrow> bool" where
  "isom_Gchains n f g h \<longleftrightarrow> (\<forall>i \<le> n. (g i) \<cong> (h (f i)))"
(* g, h are sequences of groups and f is gbijection of Nset to Nset *)

definition
 Gch_bridge :: "[nat, nat \<Rightarrow> (('a set), 'more) Group_scheme, nat \<Rightarrow> 
             (('a set), 'more) Group_scheme, nat \<Rightarrow> nat]  \<Rightarrow> bool" where
 "Gch_bridge n g h f \<longleftrightarrow> (\<forall>l \<le> n. f l \<le> n) \<and> inj_on f {i. i \<le> n} \<and> 
                         isom_Gchains n f g h"

lemma Gchain_pre:"Gchain (Suc n) g \<Longrightarrow> Gchain n g"    
apply (simp add:Gchain_def)
done

lemma (in Group) isom_unit:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; H = {\<one>}\<rbrakk>  \<Longrightarrow> 
                                    Gp G H \<cong> Gp G K \<longrightarrow> K = {\<one>}"
apply (simp add:isomorphic_def)
apply (rule impI)
apply (erule exE)
 apply (simp add:gbijec_def)
 apply (erule conjE)
 apply (simp add:gsurjec_def ginjec_def)
 apply (erule conjE)
apply (simp add:Gp_carrier)
apply (simp add:surj_to_def)
apply (cut_tac a = "f \<one>" in finite1)

apply (frule sg_unit_closed [of "K"])
 apply (frule singleton_sub[of "\<one>" "K"])
 apply (rotate_tac 4, frule sym, thin_tac "{f \<one>} = K") 
 apply (rule card_seteq[THEN sym, of "K" "{\<one>}"])
 apply (simp add:finite1) apply assumption
 apply (simp add:card1)
done

lemma isom_gch_unitsTr4:"\<lbrakk>Group F; Group G; Ugp E; F \<cong> G; F \<cong> E\<rbrakk> \<Longrightarrow>
                                 G \<cong> E"
apply (simp add:Ugp_def)
apply (erule conjE)
apply (frule isomTr1 [of "F" "G"], assumption+)
apply (rule isomTr2 [of "G" "F" "E"], assumption+)
done 

lemma isom_gch_cmp:"\<lbrakk>Gchain n g; Gchain n h; f1 \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}; 
           f2 \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}; isom_Gchains n (cmp f2 f1) g h\<rbrakk> \<Longrightarrow> 
             isom_Gchains n f1 g (cmp h f2)"
apply (simp add:isom_Gchains_def)
apply (simp add:cmp_def)
done

lemma isom_gch_transp:"\<lbrakk>Gchain n f; i \<le> n; j \<le> n; i < j\<rbrakk> \<Longrightarrow> 
                 isom_Gchains n (transpos i j) f (cmp  f (transpos i j))"
apply (rule isom_gch_cmp [of "n" "f" _ "transpos i j" "transpos i j"],
                                                                 assumption+)
 apply (rule transpos_hom, assumption+) apply simp
 apply (rule transpos_hom, assumption+) apply simp
apply (simp add:isom_Gchains_def)
apply (rule allI, rule impI) 
apply (frule less_le_trans [of "i" "j" "n"], assumption+)
apply (frule less_imp_le [of "i" "n"])
apply (frule_tac k = ia in cmp_transpos1 [of "i" "n" "j"], assumption+)
 apply simp+ 
apply (simp add:Gchain_def)
done

lemma isom_gch_units_transpTr0:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<le> n; j \<le> n;
 i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow>
 {i. i \<le> n \<and> g i \<cong> E} - {i, j} ={i. i \<le> n \<and> h i \<cong> E} - {i, j}"
apply (simp add:isom_Gchains_def)
apply (rule equalityI)
 apply (rule subsetI, simp add:CollectI)
 apply (erule conjE)+
 apply (cut_tac x = x in transpos_id_1 [of "i" "n" "j"], simp+)
apply (subgoal_tac "g x \<cong> h (transpos i j x)",
       thin_tac "\<forall>ia\<le>n. g ia \<cong> h (transpos i j ia)", simp)
apply (subgoal_tac "Group (g x)", subgoal_tac "Group (h x)")
apply (simp add:Ugp_def) apply (erule conjE)
apply (frule_tac F = "g x" and G = "h x" in isomTr1, assumption+)
apply (rule_tac F = "h x" and G = "g x" and H = E in isomTr2, assumption+)
apply (simp add:Gchain_def, simp add:Gchain_def)
 apply (thin_tac "transpos i j x = x")
 apply simp
apply (rule subsetI, simp add:CollectI)
 apply (erule conjE)+
 apply (cut_tac x = x in transpos_id_1 [of "i" "n" "j"], simp+)
apply (subgoal_tac "g x \<cong> h (transpos i j x)",
       thin_tac "\<forall>ia\<le>n. g ia \<cong> h (transpos i j ia)")
 apply simp
apply (subgoal_tac "Group (g x)",
       subgoal_tac "Group (h x)")
apply (simp add:Ugp_def) apply (erule conjE)
apply (rule_tac F = "g x" and G = "h x" and H = E in isomTr2, assumption+)
apply (simp add:Gchain_def, simp add:Gchain_def)
 apply (thin_tac "transpos i j x = x")
 apply simp
done

lemma isom_gch_units_transpTr1:"\<lbrakk>Ugp E; Gchain n g; i \<le> n; j \<le> n; g j \<cong> E; 
      i \<noteq> j\<rbrakk> \<Longrightarrow> 
      insert j ({i. i \<le> n \<and> g i \<cong> E} - {i, j}) = {i. i \<le> n \<and> g i \<cong> E} - {i}"
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply blast
apply (rule subsetI) apply (simp add:CollectI)
done

lemma isom_gch_units_transpTr2:"\<lbrakk>Ugp E; Gchain n g; i \<le> n; j \<le> n; i < j;
      g i \<cong> E\<rbrakk> \<Longrightarrow> 
      {i. i \<le> n \<and> g i \<cong> E} = insert i ({i. i \<le> n \<and>  g i \<cong> E} - {i})"
apply (rule equalityI)
 apply (rule subsetI, simp add:CollectI)
 apply (rule subsetI, simp add:CollectI)
 apply (erule disjE, simp)
 apply simp
done

lemma isom_gch_units_transpTr3:"\<lbrakk>Ugp E; Gchain n g; i \<le> n\<rbrakk>
                         \<Longrightarrow> finite ({i. i \<le> n \<and> g i \<cong> E} - {i})"
apply (rule finite_subset[of "{i. i \<le> n \<and> g i \<cong> E} - {i}" "{i. i \<le> n}"])
apply (rule subsetI, simp+)
done

lemma isom_gch_units_transpTr4:"\<lbrakk>Ugp E; Gchain n g; i \<le> n\<rbrakk>
                         \<Longrightarrow> finite ({i. i \<le> n \<and> g i \<cong> E} - {i, j})"
apply (rule finite_subset[of "{i. i \<le> n \<and> g i \<cong> E} - {i, j}" "{i. i \<le> n}"])
apply (rule subsetI, simp+)
done

lemma isom_gch_units_transpTr5_1:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<le> (n::nat);
      j \<le> n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow> g i \<cong> h j"
apply (simp add:isom_Gchains_def)
apply (frule_tac a = i in forall_spec,
       frule_tac x = i and y = j and z = n in less_le_trans,
       assumption+, simp,
       thin_tac "\<forall>ia \<le> n. g ia \<cong> h (transpos i j ia)")
apply (simp add:transpos_ij_1 [of "i" "n" "j"])
done

lemma isom_gch_units_transpTr5_2:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<le> n; 
      j \<le> n; i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow> g j \<cong> h i"
apply (simp add:isom_Gchains_def)
apply (frule_tac x = j in spec,
       thin_tac "\<forall>ia\<le> n. g ia \<cong> h (transpos i j ia)")
apply (simp add:transpos_ij_2 [of "i" "n" "j"]) 
done

lemma isom_gch_units_transpTr6:"\<lbrakk>Gchain n g; i \<le> n\<rbrakk> \<Longrightarrow> Group (g i)"
apply (simp add:Gchain_def)
done

lemma isom_gch_units_transpTr7:"\<lbrakk>Ugp E; i \<le> n; j \<le> n; g j \<cong> h i; 
      Group (h i); Group (g j); \<not> g j \<cong> E\<rbrakk> \<Longrightarrow>  \<not> h i \<cong> E"
apply (rule contrapos_pp, simp+)
apply (frule isomTr2 [of "g j" "h i" "E"], assumption+)
apply (simp add:Ugp_def)
apply assumption+
apply simp
done

lemma isom_gch_units_transpTr8_1:"\<lbrakk>Ugp E; Gchain n g; i \<le> n; j \<le> n; 
      g i \<cong> E; \<not> g j \<cong> E\<rbrakk> \<Longrightarrow> 
      {i. i \<le> n \<and> g i \<cong> E} = {i. i \<le> n \<and> g i \<cong> E} - { j }"
by auto

lemma isom_gch_units_transpTr8_2:"\<lbrakk>Ugp E; Gchain n g; i \<le> n; j \<le> n;
       \<not> g i \<cong> E; \<not> g j \<cong> E\<rbrakk> \<Longrightarrow> 
       {i. i \<le> n \<and> g i \<cong> E} = {i. i \<le> n \<and> g i \<cong> E} - {i, j }"
by auto

lemma isom_gch_units_transp:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; i \<le> n; j \<le> n; 
      i < j; isom_Gchains n (transpos i j) g h\<rbrakk> \<Longrightarrow>  
       card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and> h i \<cong> E}" 
apply (frule isom_gch_units_transpTr0 [of "E" "n" "g" "h" "i" "j"], 
        assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "g" "i"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "h" "i"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "g" "j"], assumption+)
apply (frule isom_gch_units_transpTr6 [of "n" "h" "j"], assumption+)
apply (unfold Ugp_def) apply (frule conjunct1) apply (fold Ugp_def)
apply (frule isom_gch_units_transpTr5_1 [of "E" "n" "g" "h" "i" "j"], 
                                                          assumption+)
apply (frule isom_gch_units_transpTr5_2 [of "E" "n" "g" "h" "i" "j"], 
                                                          assumption+)
apply (case_tac "g i \<cong> E")
 apply (case_tac "g j \<cong> E")  (** g i \<cong> E and g j \<cong> E **)
 apply (subst isom_gch_units_transpTr2 [of "E" "n" "g" "i" "j"], assumption+)
 apply (subst isom_gch_units_transpTr2 [of "E" "n" "h" "i" "j"], assumption+) 
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply (subst card_insert_disjoint) 
 apply (rule isom_gch_units_transpTr3, assumption+)
 apply simp
 apply (subst card_insert_disjoint)
 apply (rule isom_gch_units_transpTr3, assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1[THEN sym, of "E" "n" "g" "i" "j"], assumption+) apply simp
apply (subst isom_gch_units_transpTr1[THEN sym, of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
apply simp 
apply simp
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "g" "i" "j"], assumption+)
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "h" "j" "i"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
 apply (rule isom_gch_units_transpTr7 [of "E" "i" "n" "j" "g" "h"], 
                                                        assumption+)
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "g" "j" "i"], assumption+) apply simp
 apply (subst card_insert_disjoint)
 apply (rule isom_gch_units_transpTr4, assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "h" "i" "j"],
                                                                assumption+)
 apply (rule isom_gch_unitsTr4 [of "g i" "h j" "E"], assumption+)
 apply simp
 apply (subst card_insert_disjoint)
  apply (rule isom_gch_units_transpTr4, assumption+)
  apply simp
  apply (insert Nset_2 [of "j" "i"])
  apply simp
apply (case_tac "g j \<cong> E")
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "g" "j" "i"], assumption+)
apply (subst isom_gch_units_transpTr8_1 [of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply (rule isom_gch_units_transpTr7 [of "E" "j" "n" "i" "g" "h"], assumption+)
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "g" "i" "j"],
                                                              assumption+)
 apply simp
 apply (subst isom_gch_units_transpTr1 [THEN sym, of "E" "n" "h" "j" "i"],
                                                              assumption+)
 apply (rule isom_gch_unitsTr4 [of "g j" "h i" "E"], assumption+)
 apply simp apply simp
 apply (subst isom_gch_units_transpTr8_2 [of "E" "n" "g" "i" "j"], assumption+)
 apply (subst isom_gch_units_transpTr8_2 [of "E" "n" "h" "i" "j"], assumption+)
 apply (rule isom_gch_units_transpTr7[of "E" "i" "n" "j" "g" "h"], assumption+)
 apply (rule isom_gch_units_transpTr7[of "E" "j" "n" "i" "g" "h"], assumption+)
apply simp
done

lemma TR_isom_gch_units:"\<lbrakk>Ugp E; Gchain n f; i \<le> n; j \<le> n; i < j\<rbrakk> \<Longrightarrow>
      card {k. k \<le> n \<and> f k \<cong> E} = card {k. k \<le> n \<and> 
      (cmp f (transpos i j)) k \<cong> E}" 
apply (frule isom_gch_transp [of "n" "f" "i" "j"], assumption+)
(* apply (subgoal_tac "Gchain n (cmp f (transpos i j))") *)
 apply (rule isom_gch_units_transp [of "E" "n" "f" _ "i" "j"], assumption+)
 apply (simp add:Gchain_def)
 apply (rule allI, rule impI)
 apply (simp add:cmp_def)
apply (cut_tac l = l in transpos_mem [of "i" "n" "j"],
       frule_tac x = i and y = j and z = n in less_le_trans, assumption+,
       simp)
 apply simp+
done

lemma TR_isom_gch_units_1:"\<lbrakk>Ugp E; Gchain n f; i \<le> n; j \<le> n; i < j\<rbrakk>  \<Longrightarrow>  
      card {k. k \<le> n \<and> f k \<cong> E} = card {k. k \<le> n \<and> f (transpos i j k) \<cong> E}" 
apply (frule TR_isom_gch_units [of "E" "n" "f" "i" "j"], assumption+)
 apply (simp add:cmp_def)
done

lemma isom_tgch_unitsTr0_1:"\<lbrakk>Ugp E; Gchain (Suc n) g; g (Suc n) \<cong> E\<rbrakk> \<Longrightarrow> 
      {i. i \<le> (Suc n) \<and> g i \<cong> E} = insert (Suc n) {i. i \<le> n \<and> g i \<cong> E}"
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (case_tac "x = Suc n") apply simp
 apply (erule conjE) apply simp 
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (erule disjE) apply simp
apply simp
done

lemma isom_tgch_unitsTr0_2:"Ugp E  \<Longrightarrow> finite ({i. i \<le> (n::nat) \<and> g i \<cong> E})"
apply (rule finite_subset[of "{i. i \<le> n \<and> g i \<cong> E}" "{i. i \<le> n}"])
apply (rule subsetI, simp+)
done

lemma isom_tgch_unitsTr0_3:"\<lbrakk>Ugp E; Gchain (Suc n) g; \<not> g (Suc n) \<cong> E\<rbrakk>
      \<Longrightarrow> {i. i \<le> (Suc n) \<and> g i \<cong> E} = {i. i \<le> n \<and> g i \<cong> E}"
apply (rule equalityI)
apply (rule subsetI, simp add:CollectI)
apply (case_tac "x = Suc n", simp, erule conjE)
 apply arith
apply (rule subsetI, simp add:CollectI) 
done

lemma isom_tgch_unitsTr0:"\<lbrakk>Ugp E; 
      card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and> h i \<cong> E}; 
      Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f; 
      f (Suc n) = Suc n\<rbrakk> \<Longrightarrow> 
      card {i. i \<le> (Suc n) \<and> g i \<cong> E} = 
                                card {i. i \<le> (Suc n) \<and> h i \<cong> E}"
apply (erule conjE)+
apply (frule isom_gch_units_transpTr6 [of "Suc n" "g" "Suc n"])
apply (simp add:n_in_Nsetn)
apply (frule isom_gch_units_transpTr6 [of "Suc n" "h" "Suc n"])
apply (simp add:n_in_Nsetn)
apply (simp add:Gch_bridge_def isom_Gchains_def)
 apply (erule conjE)+
 apply (rotate_tac -1, 
        frule_tac a = "Suc n" in forall_spec,
        thin_tac "\<forall>i\<le>Suc n. g i \<cong> h (f i)", simp+,
        thin_tac "\<forall>i\<le>Suc n. g i \<cong> h (f i)")
apply (case_tac "g (Suc n) \<cong> E")
 apply (subst isom_tgch_unitsTr0_1 [of "E" "n" "g"], assumption+)
 apply (subst isom_tgch_unitsTr0_1 [of "E" "n" "h"], assumption+) 
 apply (frule isom_gch_unitsTr4 [of "g (Suc n)" "h (Suc n)" "E"], assumption+)
apply (subst card_insert_disjoint) 
 apply (rule finite_subset[of "{i. i \<le> n \<and> g i \<cong> E}" "{i. i \<le> n}"])
 apply (rule subsetI, simp) apply (simp)
 apply simp
apply (subst card_insert_disjoint) 
 apply (rule finite_subset[of "{i. i \<le> n \<and> h i \<cong> E}" "{i. i \<le> n}"])
 apply (rule subsetI, simp) apply simp apply simp
 apply simp
 apply (cut_tac isom_gch_units_transpTr7[of E "Suc n" "Suc n" "Suc n" g h])
 apply (subgoal_tac "{i. i \<le> Suc n \<and> g i \<cong> E} = {i. i \<le> n \<and> g i \<cong> E}",
        subgoal_tac "{i. i \<le> Suc n \<and> h i \<cong> E} = {i. i \<le> n \<and> h i \<cong> E}",
        simp)
 apply (rule equalityI, rule subsetI, simp,
        erule conjE, case_tac "x = Suc n", simp,
        frule_tac x = x and y = "Suc n" in le_imp_less_or_eq,
        thin_tac "x \<le> Suc n", simp,
        rule subsetI, simp)
 apply (rule equalityI, rule subsetI, simp,
        erule conjE, case_tac "x = Suc n", simp,
        frule_tac m = x and n = "Suc n" in noteq_le_less, assumption+,
        simp,        
        rule subsetI, simp)    
 apply simp+
done

lemma isom_gch_unitsTr1_1:" \<lbrakk>Ugp E; Gchain (Suc n) g \<and>  Gchain (Suc n) h 
       \<and> Gch_bridge (Suc n) g h f; f (Suc n) = Suc n\<rbrakk> \<Longrightarrow> 
           Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f"
apply (erule conjE)+
apply (frule Gchain_pre [of "n" "g"])
apply (frule Gchain_pre [of "n" "h"])
apply simp
apply (simp add:Gch_bridge_def) apply (erule conjE)+
apply (rule conjI)
apply (rule Nset_injTr2, assumption+)
apply (rule conjI)
apply (rule Nset_injTr1, assumption+)
apply (simp add:isom_Gchains_def)
done

lemma isom_gch_unitsTr1_2:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; inj_on f {i. i\<le>(Suc n)};
        \<forall>l \<le> (Suc n). f l \<le> (Suc n)\<rbrakk> \<Longrightarrow> 
        (cmp (transpos (f (Suc n)) (Suc n)) f) (Suc n) = Suc n"
apply (simp add:cmp_def)
apply (cut_tac n_in_Nsetn[of "Suc n"], simp)
apply (frule_tac a = "Suc n" in forall_spec, 
      simp,
      thin_tac "\<forall>l\<le>Suc n. f l \<le> Suc n") 
apply (rule transpos_ij_1, assumption+, simp+)
done

lemma isom_gch_unitsTr1_3:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; 
     \<forall>l \<le> (Suc n). f l \<le> (Suc n); inj_on f {i. i \<le> (Suc n)}\<rbrakk> \<Longrightarrow> 
      inj_on (cmp (transpos (f (Suc n)) (Suc n)) f) {i. i \<le> (Suc n)}"
apply (cut_tac n_in_Nsetn[of "Suc n"], simp)
apply (frule_tac a = "Suc n" in forall_spec, simp)
apply (frule transpos_hom [of "f (Suc n)" "Suc n" "Suc n"], simp+)
    thm transpos_inj
apply (cut_tac transpos_inj [of "f (Suc n)" "Suc n" "Suc n"])
apply (cut_tac cmp_inj_1 [of f "{i. i \<le> (Suc n)}" "{i. i \<le> (Suc n)}"
       "transpos (f (Suc n)) (Suc n)" "{i. i \<le> (Suc n)}"])
apply simp+
done

lemma isom_gch_unitsTr1_4:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; inj_on f {i. i\<le>(Suc n)};
                   \<forall>l \<le> (Suc n). f l \<le> (Suc n)\<rbrakk> \<Longrightarrow> 
                    inj_on (cmp (transpos (f (Suc n)) (Suc n)) f) {i. i \<le> n}"
apply (frule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (frule isom_gch_unitsTr1_2 [of "E" "f" "n"], assumption+)
apply (rule Nset_injTr1 [of "n" "(cmp (transpos (f (Suc n)) (Suc n)) f)"])
apply (rule allI, rule impI)
apply (simp add:cmp_def)  
apply (cut_tac l = "f l" in transpos_mem[of "f (Suc n)" "Suc n" "Suc n"], 
       simp+)
done

lemma isom_gch_unitsTr1_5:"\<lbrakk>Ugp E; Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> 
      Gch_bridge (Suc n) g h f; f (Suc n) \<noteq> Suc n \<rbrakk> \<Longrightarrow> 
      Gchain n g \<and> Gchain n (cmp h (transpos (f (Suc n)) (Suc n))) \<and> 
      Gch_bridge n g (cmp h (transpos (f (Suc n)) (Suc n))) 
                               (cmp (transpos (f (Suc n)) (Suc n)) f)"
apply (erule conjE)+ 
apply (simp add:Gchain_pre [of "n" "g"])
apply (rule conjI)
apply (simp add:Gchain_def) apply (rule allI, rule impI)
apply (simp add:Gch_bridge_def) apply (frule conjunct1)
apply (fold Gch_bridge_def)
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply (cut_tac l = l in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"])
      apply simp+
apply (simp add:cmp_def)

apply (simp add:Gch_bridge_def)
apply (erule conjE)+
apply (rule conjI)
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply (rule allI, rule impI, simp add:cmp_def)
apply (frule isom_gch_unitsTr1_2 [of "E" "f" "n"], assumption+)
apply (frule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (cut_tac l = "f l" in transpos_mem[of "f (Suc n)" "Suc n" "Suc n"])
 apply simp+ 
 apply (simp add:inj_on_def[of "cmp (transpos (f (Suc n)) (Suc n)) f"])
 apply (rotate_tac -2,
        frule_tac a = "Suc n" in forall_spec, simp) apply (
        thin_tac "\<forall>x\<le>Suc n.
            \<forall>y\<le>Suc n.
               cmp (transpos (f (Suc n)) (Suc n)) f x =
               cmp (transpos (f (Suc n)) (Suc n)) f y \<longrightarrow>
               x = y") apply (
        rotate_tac -1,
        frule_tac x = l in spec) apply (
        thin_tac "\<forall>y\<le>Suc n.
            cmp (transpos (f (Suc n)) (Suc n)) f (Suc n) =
            cmp (transpos (f (Suc n)) (Suc n)) f y \<longrightarrow>
            Suc n = y")
apply (metis Nfunc_iNJTr comp_transpos_1 le_SucE le_SucI le_refl less_Suc_eq_le transpos_ij_2)
apply (simp add:isom_gch_unitsTr1_4)
apply (simp add:isom_Gchains_def[of "n"])
apply (rule allI, rule impI)
apply (simp add:cmp_def)
apply (cut_tac l = "f i" in transpos_mem[of "f (Suc n)" "Suc n" "Suc n"])
       apply simp+
apply (cut_tac k = "f i" in cmp_transpos1 [of "f (Suc n)" "Suc n" "Suc n"])
       apply simp+
 apply (simp add:cmp_def)
apply (thin_tac "transpos (f (Suc n)) (Suc n) (transpos (f (Suc n)) (Suc n) (f i)) = f i")
apply (simp add:isom_Gchains_def)
done

lemma isom_gch_unitsTr1_6:"\<lbrakk>Ugp E; f (Suc n) \<noteq> Suc n; Gchain (Suc n) g \<and> 
       Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f\<rbrakk>  \<Longrightarrow> Gchain (Suc n) g \<and>
          Gchain (Suc n) (cmp h (transpos (f (Suc n)) (Suc n))) \<and>
          Gch_bridge (Suc n) g (cmp h (transpos (f (Suc n)) (Suc n)))
           (cmp (transpos (f (Suc n)) (Suc n)) f)"
apply (erule conjE)+
apply simp
apply (simp add:Gch_bridge_def, frule conjunct1)
apply (frule conjunct2, fold Gch_bridge_def, erule conjE)
apply (rule conjI)
apply (thin_tac "Gchain (Suc n) g")
apply (simp add:Gchain_def, rule allI, rule impI)
apply (simp add:cmp_def)
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply (cut_tac l = l in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"],
       simp+)
apply (simp add:Gch_bridge_def)
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply (rule conjI)
apply (rule allI, rule impI)
apply (simp add:cmp_def)
apply (rule_tac l = "f l" in transpos_mem [of "f (Suc n)" "Suc n" "Suc n"],
       simp+)
apply (rule conjI)
apply (rule isom_gch_unitsTr1_3 [of "E" "f" "n"], assumption+)
apply (simp add:isom_Gchains_def, rule allI, rule impI)
apply (simp add:cmp_def)
apply (cut_tac k = "f i" in cmp_transpos1 [of "f (Suc n)" "Suc n" "Suc n"], 
       simp+) 
apply (simp add:cmp_def)
done

lemma isom_gch_unitsTr1_7_0:"\<lbrakk>Gchain (Suc n) h; k \<noteq> Suc n; k \<le> (Suc n)\<rbrakk>
 \<Longrightarrow> Gchain (Suc n) (cmp h (transpos k (Suc n)))"
apply (simp add:Gchain_def)
apply (rule allI, rule impI)
apply (simp add:cmp_def) 
apply (insert n_in_Nsetn [of "Suc n"])
apply (cut_tac l = l in transpos_mem [of "k" "Suc n" "Suc n"])
apply simp+
done

lemma isom_gch_unitsTr1_7_1:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; k \<le> (Suc n)\<rbrakk>
 \<Longrightarrow> {i. i \<le> (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} - {k , Suc n} =
                            {i. i \<le> (Suc n) \<and> h i \<cong> E} - {k , Suc n}"
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply auto
apply (frule_tac x = x in transpos_id_1 [of "k" "Suc n" "Suc n"], simp+)
apply (simp add:cmp_def)
apply (simp add:cmp_def)
apply (cut_tac x = x in transpos_id_1 [of "k" "Suc n" "Suc n"], simp+)
done

lemma isom_gch_unitsTr1_7_2:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
            k \<le> (Suc n);  h (Suc n) \<cong> E\<rbrakk> \<Longrightarrow> 
                          cmp h (transpos k (Suc n)) k \<cong> E"
apply (simp add:cmp_def)
apply (subst transpos_ij_1 [of "k" "Suc n" "Suc n"], simp+)
done

lemma isom_gch_unitsTr1_7_3:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
       k \<le> (Suc n); h k \<cong> E\<rbrakk> \<Longrightarrow> cmp h (transpos k (Suc n)) (Suc n) \<cong> E"
apply (simp add:cmp_def)
apply (subst transpos_ij_2 [of "k" "Suc n" "Suc n"], assumption+)
apply simp apply assumption+
done

lemma isom_gch_unitsTr1_7_4:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n;  
      k \<le> (Suc n); \<not> h (Suc n) \<cong> E\<rbrakk> \<Longrightarrow>
                \<not>  cmp h (transpos k (Suc n)) k \<cong> E"
apply (rule contrapos_pp, simp+)
apply (simp add:cmp_def)
apply (insert n_in_Nsetn [of "Suc n"])
apply (simp add: transpos_ij_1 [of "k" "Suc n" "Suc n"])
done

lemma isom_gch_unitsTr1_7_5:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
      k \<le> (Suc n); \<not> h k \<cong> E\<rbrakk> \<Longrightarrow>
              \<not>  cmp h (transpos k (Suc n)) (Suc n) \<cong> E"
apply (rule contrapos_pp, simp+)
apply (simp add:cmp_def)
apply (insert n_in_Nsetn [of "Suc n"])
apply (simp add:transpos_ij_2 [of "k" "Suc n" "Suc n"])
done

lemma isom_gch_unitsTr1_7_6:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
    k \<le> (Suc n); h (Suc n) \<cong> E; h k \<cong> E\<rbrakk> \<Longrightarrow> 
    {i. i \<le> (Suc n) \<and>  h i \<cong> E} = 
    insert k (insert (Suc n) ({i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n}))" 
apply auto
done

lemma isom_gch_unitsTr1_7_7:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
      k \<le> (Suc n); h (Suc n) \<cong> E; \<not> h k \<cong> E\<rbrakk> \<Longrightarrow> 
      {i. i \<le> (Suc n) \<and>  h i \<cong> E} = 
       insert (Suc n) ({i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n})" 
apply auto
done

lemma isom_gch_unitsTr1_7_8:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
      k \<le> (Suc n); \<not> h (Suc n) \<cong> E;  h k \<cong> E\<rbrakk> \<Longrightarrow> 
     {i. i \<le> (Suc n) \<and>  h i \<cong> E} = 
       insert k ({i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n})"
apply auto
done

lemma isom_gch_unitsTr1_7_9:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
      k \<le> (Suc n); \<not> h (Suc n) \<cong> E; \<not> h k \<cong> E\<rbrakk> \<Longrightarrow>
      {i. i \<le> (Suc n) \<and>  h i \<cong> E} =
      {i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n}" 
apply auto
done

lemma isom_gch_unitsTr1_7:"\<lbrakk>Ugp E; Gchain (Suc n) h; k \<noteq> Suc n; 
    k \<le> (Suc n)\<rbrakk> \<Longrightarrow> card {i. i \<le> (Suc n) \<and> 
    cmp h (transpos k (Suc n)) i \<cong> E} =  card {i. i \<le> (Suc n) \<and> h i \<cong> E}"
apply (cut_tac finite_Collect_le_nat[of "Suc n"])
apply (frule isom_gch_unitsTr1_7_1 [of "E" "n" "h" "k"], assumption+)
apply (cut_tac n_in_Nsetn[of "Suc n"])
apply (case_tac "h (Suc n) \<cong> E")
 apply (case_tac "h k \<cong> E")
 apply (subst isom_gch_unitsTr1_7_6 [of "E" "n" "h" "k"], assumption+)
 apply (frule isom_gch_unitsTr1_7_2 [of "E" "n" "h" "k"], assumption+)
 apply (frule isom_gch_unitsTr1_7_3 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_6 [of "E" "n" "cmp h (transpos k (Suc n))" "k"], assumption+)
apply (subst card_insert_disjoint) 
apply (rule finite_subset[of "insert (Suc n) 
           ({i. i \<le> (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} -
           {k, Suc n})" "{i. i \<le> (Suc n)}"])
 apply (rule subsetI, simp)
 apply (erule disjE)
        apply simp apply simp apply assumption
        apply simp

apply (subst card_insert_disjoint)+
 apply (rule finite_subset[of "{i. i \<le> (Suc n) \<and> cmp h (transpos k (Suc n)) i \<cong> E} - {k, Suc n}" "{i. i \<le> (Suc n)}"])
 apply (rule subsetI, simp) apply assumption
 apply simp

apply (subst card_insert_disjoint)+
 apply (rule finite_subset[of "insert (Suc n) ({i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n})" "{i. i \<le> (Suc n)}"])
 apply (rule subsetI, simp) apply (erule disjE, simp add:n_in_Nsetn) apply simp
 apply assumption apply simp

apply (subst card_insert_disjoint)
  apply (rule finite_subset[of "{i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n}"
         "{i. i \<le> (Suc n)}"])
  apply (rule subsetI, simp) apply assumption apply simp
  apply simp
     
apply (subst isom_gch_unitsTr1_7_7[of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0[of "n" "h" "k"], assumption+)
apply (subst isom_gch_unitsTr1_7_8[of "E" "n" "cmp h (transpos k (Suc n))" 
        "k"], assumption+)
  apply (subst cmp_def)
  apply (subst transpos_ij_2[of "k" "Suc n" "Suc n"], assumption+, simp+)
 apply (simp add:cmp_def, simp add:transpos_ij_1) 

apply (subst card_insert_disjoint)
  apply (rule finite_subset[of "{i. i \<le> (Suc n) \<and> 
         cmp h (transpos k (Suc n)) i \<cong> E} - {k, Suc n}" "{i. i \<le> (Suc n)}"])
  apply (rule subsetI, simp) apply assumption apply simp
apply (subst card_insert_disjoint)
  apply (rule finite_subset[of "{i. i \<le> (Suc n) \<and> h i \<cong> E} - {k, Suc n}" 
         "{i. i \<le> (Suc n)}"])
  apply (rule subsetI, simp) apply assumption apply simp
  apply simp

apply (case_tac "h k \<cong> E")
apply (subst isom_gch_unitsTr1_7_8 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_3 [of "E" "n" "h" "k"], assumption+) 
apply (frule isom_gch_unitsTr1_7_4 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_7 [of "E" "n" "cmp h (transpos k (Suc n))" 
                                                     "k"], assumption+)
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp
apply (subst card_insert_disjoint)
apply (rule isom_gch_units_transpTr4, assumption+) apply simp apply simp
apply (subst isom_gch_unitsTr1_7_9 [of "E" "n" "h" "k"], assumption+)
apply (frule_tac isom_gch_unitsTr1_7_4 [of "E" "n" "h" "k"], assumption+)
apply (frule_tac isom_gch_unitsTr1_7_5 [of "E" "n" "h" "k"], assumption+)
apply (frule isom_gch_unitsTr1_7_0 [of "n" "h" "k" ], assumption+)
apply (subst isom_gch_unitsTr1_7_9 [of "E" "n" " cmp h (transpos k (Suc n))" "k"], assumption+) apply simp
done

lemma isom_gch_unitsTr1:"Ugp E \<Longrightarrow> \<forall>g. \<forall>h. \<forall>f. Gchain n g \<and> 
      Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>  card {i. i \<le> n \<and> g i \<cong> E} = 
           card {i. i \<le> n \<and> h i \<cong> E}"
apply (induct_tac n)
 apply (clarify)
 apply (simp add:Gch_bridge_def isom_Gchains_def Collect_conv_if)
 apply rule
  apply (simp add:Gchain_def)
  apply(metis isom_gch_unitsTr4)
 apply (simp add:Gchain_def)
 apply (metis Ugp_def isomTr2)
(***** n ******)
 apply (rule allI)+  apply (rule impI)
 (** n ** case f (Suc n) = Suc n **)
 apply (case_tac "f (Suc n) = Suc n") 
 apply (subgoal_tac "card {i. i \<le> n \<and> g i \<cong> E} =  card {i. i \<le> n \<and> h i \<cong> E}")
 apply (thin_tac " \<forall>g h f.
             Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>
             card {i. i \<le> n \<and> g i \<cong> E} =
             card {i. i \<le> n \<and> h i \<cong> E}")
apply (rule isom_tgch_unitsTr0, assumption+)
 apply (frule_tac n = n and g = g and h = h and f = f in 
            isom_gch_unitsTr1_1 [of "E"], assumption+)
 apply (rotate_tac -1) 
 apply (thin_tac "Gchain (Suc n) g \<and> Gchain (Suc n) h \<and> Gch_bridge (Suc n) g h f")
 apply blast
  (**** n **** f (Suc n) \<noteq> Suc n ***) 
 apply (frule_tac n = n and g = g and h = h and f = f in isom_gch_unitsTr1_5 [of "E"], assumption+) 
apply (subgoal_tac "card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and>  
                       (cmp h (transpos (f (Suc n)) (Suc n))) i \<cong> E}")
prefer 2 apply blast
 apply (thin_tac "\<forall>g h f.
             Gchain n g \<and> Gchain n h \<and> Gch_bridge n g h f \<longrightarrow>
             card {i. i \<le> n \<and> g i \<cong> E} =
             card {i. i \<le> n \<and> h i \<cong> E}")
 apply (thin_tac "Gchain n g \<and>
          Gchain n (cmp h (transpos (f (Suc n)) (Suc n))) \<and>
          Gch_bridge n g (cmp h (transpos (f (Suc n)) (Suc n)))
           (cmp (transpos (f (Suc n)) (Suc n)) f)")
apply (subgoal_tac "cmp (transpos (f (Suc n)) (Suc n)) f (Suc n) = Suc n")
apply (frule_tac n = n and g = g and h = "cmp h (transpos (f (Suc n)) (Suc n))" and f = "cmp (transpos (f (Suc n)) (Suc n)) f"  in  isom_tgch_unitsTr0 [of "E"], assumption+)
apply (rule isom_gch_unitsTr1_6, assumption+)
 apply (thin_tac "card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and>
                          cmp h (transpos (f (Suc n)) (Suc n)) i \<cong> E}")
prefer 2 
 apply (erule conjE)+
 apply (simp add:Gch_bridge_def) apply (erule conjE)+
 apply (rule isom_gch_unitsTr1_2, assumption+)
apply simp
apply (erule conjE)+
apply (rule isom_gch_unitsTr1_7, assumption+)
apply (simp add:Gch_bridge_def)
done
 
lemma isom_gch_units:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; Gch_bridge n g h f\<rbrakk> \<Longrightarrow>  
      card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and> h i \<cong> E}"
apply (simp add:isom_gch_unitsTr1)
done

lemma isom_gch_units_1:"\<lbrakk>Ugp E; Gchain n g; Gchain n h; \<exists>f. Gch_bridge n g h f\<rbrakk>
 \<Longrightarrow>  card {i. i \<le> n \<and> g i \<cong> E} = card {i. i \<le> n \<and> h i \<cong> E}"
apply (auto del:equalityI)
apply (simp add:isom_gch_units)
done

section "Jordan Hoelder theorem"

subsection \<open>\<open>Rfn_tools\<close>. Tools to treat refinement of a cmpser, rtos.\<close>

lemma rfn_tool1:"\<lbrakk> 0 < (r::nat); (k::nat) = i * r + j; j < r \<rbrakk> 
                                                  \<Longrightarrow> (k div r) = i"  
proof -
 assume p1: "0 < r" and p2: "k = i * r + j" and p3: "j < r"
 from p1 and p2 have q1: "(j + i * r) div r = i + j div r" 
 apply (simp add:div_mult_self1 [of "r" "j" "i" ]) done
 from p1 and p3 have q2: "j div r = 0"
  apply (simp add:div_if) done
 from q1 and q2 have q3:"(j + i * r) div r = i"
  apply simp done
 from q3 have q4: "(i * r + j) div r = i" apply (simp add:add.commute)
  done
 from p2 and q4 show ?thesis
  apply simp 
 done
qed

lemma pos_mult_pos:"\<lbrakk> 0 < (r::nat); 0 < s\<rbrakk> \<Longrightarrow> 0 < r * s"
by simp

lemma rfn_tool1_1:"\<lbrakk> 0 < (r::nat); j < r \<rbrakk> 
                             \<Longrightarrow> (i * r + j) div r = i"
apply (rule rfn_tool1 [of "r" "i * r + j" "i" "j"], assumption+)  
apply simp+
done

lemma rfn_tool2:"(a::nat) < s \<Longrightarrow> a \<le> s - Suc 0"
 apply (rule less_le_diff) apply simp+
done

lemma rfn_tool3:"(0::nat) \<le> m \<Longrightarrow> (m + n) - n = m"
apply auto
done

lemma rfn_tool11:"\<lbrakk>0 < b; (a::nat) \<le> b - Suc 0\<rbrakk> \<Longrightarrow> a < b"
 apply (frule le_less_trans [of "a" "b - Suc 0" "b"])
 apply simp+
done

lemma  rfn_tool12:"\<lbrakk>0 < (s::nat); (i::nat) mod s = s - 1 \<rbrakk> \<Longrightarrow>
                     Suc (i div s) = (Suc i) div s "
proof -
 assume p1:"0 < s" and p2:"i mod s = s - 1"
 have q1:"i div s * s + i mod s = i"
   apply (insert div_mult_mod_eq [of "i" "s"]) 
   apply simp done
 have q2:"Suc (i div s * s + i mod s) = i div s * s + Suc (i mod s)"
  apply (insert add_Suc_right [THEN sym, of "i div s * s" "i mod s"])
  apply assumption done
 from p1 and p2 and q2 have q3:"Suc (i div s * s + i mod s) = i div s * s + s"
  apply simp done
 from q3 have q4:"Suc (i div s * s + i mod s) = Suc (i div s) * s "
  apply simp done
 from p1 and q1 and q4 show ?thesis  
 apply auto
 done
qed

lemma  rfn_tool12_1:"\<lbrakk>0 < (s::nat); (l::nat) mod s < s - 1 \<rbrakk> \<Longrightarrow>
                     Suc (l mod s) = (Suc l) mod s "
apply (insert div_mult_mod_eq [of "l" "s"])
apply (insert add_Suc_right [THEN sym, of "l div s * s" "l mod s"])
apply (insert mod_mult_self1  [of "Suc (l mod s)" "l div s" "s"])
apply (frule Suc_mono [of "l mod s" "s - 1"]) apply simp
done

lemma  rfn_tool12_2:"\<lbrakk>0 < (s::nat); (i::nat) mod s = s - Suc 0\<rbrakk> \<Longrightarrow>
                                               (Suc i) mod s = 0" 
apply (insert div_mult_mod_eq [THEN sym, of "i" "s"])
apply (insert add_Suc_right [THEN sym, of "i div s * s" "i mod s"])
apply simp
done

lemma rfn_tool13:"\<lbrakk> (0::nat) < r; a = b \<rbrakk> \<Longrightarrow> a mod r = b mod r"
apply simp
done

lemma rfn_tool13_1:"\<lbrakk> (0::nat) < r; a = b \<rbrakk> \<Longrightarrow> a div r = b div r"
apply simp
done

lemma div_Tr1:"\<lbrakk> (0::nat) < r; 0 < s; l \<le> s * r\<rbrakk> \<Longrightarrow> l div s \<le> r"
 apply (frule_tac m = l and n = "s * r" and k = s in div_le_mono)
 apply simp
done

lemma div_Tr2:"\<lbrakk>(0::nat) < r; 0 < s; l < s * r\<rbrakk> \<Longrightarrow> l div s \<le> r - Suc 0"
apply (rule contrapos_pp, simp+)
apply (simp add: not_less [symmetric, of "l div s" "r - Suc 0"])
apply (frule Suc_leI [of "r - Suc 0" "l div s"])
apply simp
apply (frule less_imp_le [of "l" "s * r"])
apply (frule div_le_mono [of "l" "s * r" "s"]) apply simp
apply (insert div_mult_mod_eq [THEN sym, of "l" "s"])
apply (frule sym) apply (thin_tac "r = l div s")
apply simp apply (simp add:mult.commute [of "r" "s"])
done

lemma div_Tr3:"\<lbrakk>(0::nat) < r; 0 < s; l < s * r\<rbrakk> \<Longrightarrow> Suc (l div s) \<le> r"
apply (frule_tac div_Tr2[of "r" "s"], assumption+,
       cut_tac n1 = "l div s" and m1 = "r - Suc 0" in  Suc_le_mono[THEN sym])
apply simp
done

lemma div_Tr3_1:"\<lbrakk>(0::nat) < r; 0 < s; l mod s = s - 1\<rbrakk> \<Longrightarrow>  Suc l div s = Suc (l div s)"
apply (frule rfn_tool12 [of "s" "l"], assumption+)
 apply (rotate_tac -1) apply simp
done

lemma div_Tr3_2:"\<lbrakk>(0::nat) < r; 0 < s; l mod s < s - 1\<rbrakk> \<Longrightarrow> 
                                       l div s = Suc l div s"
apply (frule Suc_mono [of "l mod s" "s - 1"]) apply simp
apply (cut_tac div_mult_mod_eq [of "l" "s"])
apply (cut_tac add_Suc_right [THEN sym, of "l div s * s" "l mod s"])
apply (cut_tac zero_less_Suc[of "l mod s"],
       frule less_trans[of "0" "Suc (l mod s)" "s"], assumption+)
apply (frule rfn_tool13_1 [of "s" "Suc (l div s * s + l mod s)" "l div s * s + Suc (l mod s)"], assumption+)
apply (subgoal_tac "s \<noteq> 0")
apply (frule div_mult_self1 [of "s" "Suc (l mod s)" "l div s"])
apply simp_all
done

lemma mod_div_injTr:"\<lbrakk>(0::nat) < r; x mod r = y mod r; x div r = y div r\<rbrakk>
                      \<Longrightarrow> x = y"
apply (cut_tac div_mult_mod_eq[of "x" "r"])
apply simp
done

definition
  rtos :: "[nat, nat] \<Rightarrow> (nat \<Rightarrow> nat)" where
  "rtos r s i = (if i < r * s then (i mod s) * r + i div s else r * s)"
 
lemma rtos_hom0:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<le> (r * s - Suc 0)\<rbrakk> \<Longrightarrow>
   i div s < r" 
apply (frule div_Tr2 [of "r" "s" "i"], assumption+)
apply (simp add:mult.commute [of "r" "s"])
apply (rule le_less_trans, assumption+) apply simp 
apply (rule le_less_trans, assumption+) apply simp
done

lemma rtos_hom1:"\<lbrakk>(0::nat) < r; 0 < s; l \<le> (r * s - Suc 0)\<rbrakk> \<Longrightarrow> 
 (rtos r s) l \<le> (s * r - Suc 0)"
apply (simp add:rtos_def)
apply (frule le_less_trans [of "l" "r * s - Suc 0" "r * s"])
 apply simp
 apply simp 
apply (frule mod_less_divisor [of "s" "l"])
 apply (frule less_le_diff [of "l mod s" "s"])
 apply (frule_tac i = "l mod s" and j = "s - Suc 0" and k = r and l = r in
         mult_le_mono, simp)
 apply (frule_tac i = "l mod s * r" and j = "(s - Suc 0) * r" and k = "l div s" and l = "r - Suc 0" in add_le_mono)
 apply (rule div_Tr2, assumption+, simp add:mult.commute)
 apply (simp add:diff_mult_distrib)
done

lemma rtos_hom2:"\<lbrakk>(0::nat) < r; (0::nat) < s; l \<le> (r * s - Suc 0)\<rbrakk> \<Longrightarrow> 
 rtos r s l \<le> (r * s - Suc 0)"
apply (insert  rtos_hom1 [of "r" "s"]) apply simp
apply (simp add:mult.commute)
done

lemma rtos_hom3:"\<lbrakk>(0::nat) < r; 0 < s; i \<le> (r * s - Suc 0) \<rbrakk> \<Longrightarrow>
                   (rtos r s i div r) = i mod s"
apply (simp add:rtos_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"])
 apply simp apply simp
apply (auto simp add: div_mult2_eq [symmetric] mult.commute)
done

lemma rtos_hom3_1:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<le> (r * s - Suc 0) \<rbrakk> \<Longrightarrow>
  (rtos r s i mod  r) = i div s"
apply (simp add:rtos_def)
apply (simp add:rfn_tool11 [of "r * s" "i"])
 apply (frule rtos_hom0 [of "r" "s" "i"], assumption+)
 apply (simp add:mem_of_Nset)
done

lemma rtos_hom5:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<le> (r *s - Suc 0); 
i div s = r - Suc 0 \<rbrakk> \<Longrightarrow> Suc (rtos r s i) div r = Suc (i mod s)"
 apply (frule mult_less_mono2[of "0" "s" "r"],
        simp only:mult.commute,
        simp only:mult_0_right)
 apply (frule rfn_tool11 [of "r * s" "i"], assumption+)
 apply (simp add: rtos_def)
done

lemma rtos_hom7:"\<lbrakk>(0::nat) < r; (0::nat) < s; i \<le> (r * s - Suc 0); 
                   i div s = r - Suc 0 \<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = 0"
apply (frule rtos_hom0 [of "r" "s" "i"], assumption+)
apply (simp add: rtos_def) 
apply (frule mult_less_mono2[of "0" "s" "r"],
        simp only:mult.commute,
        simp only:mult_0_right)
apply (simp add: rfn_tool11 [of "r * s" "i"])
done

lemma rtos_inj:"\<lbrakk> (0::nat) < r; (0::nat) < s \<rbrakk> \<Longrightarrow> 
                   inj_on (rtos r s) {i. i \<le> (r * s - Suc 0)}"
apply (simp add:inj_on_def) 
apply ((rule allI, rule impI)+, rule impI)
 apply (frule_tac i1 = x in rtos_hom3_1[THEN sym, of "r" "s"], assumption+,
        frule_tac i1 = x in rtos_hom3[THEN sym, of "r" "s"], assumption+,
        frule_tac i = y in rtos_hom3_1[of "r" "s"], assumption+,
        frule_tac i = y in rtos_hom3[of "r" "s"], assumption+)
 apply simp
 apply (rule_tac x = x and y = y in mod_div_injTr[of "s"], assumption+)        
done

lemma rtos_rs_Tr1:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow> rtos r s (r * s) = r * s"
apply (simp add:rtos_def)
done

lemma rtos_rs_Tr2:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow>
                                 \<forall>l \<le> (r * s). rtos r s l \<le> (r * s)"
apply (rule allI, rule impI)
 apply (case_tac "l = r * s", simp add:rtos_rs_Tr1)
 apply (frule le_imp_less_or_eq) 
 apply (thin_tac "l \<le> r * s", simp)
 apply (frule mult_less_mono2[of "0" "s" "r"],
        simp only:mult.commute,
        simp only:mult_0_right)
 apply (frule_tac  r = r and s = s and l = l in rtos_hom2, assumption+)
 apply (rule less_le_diff)
 apply simp
 apply (metis le_pre_le) 
done
    
lemma rtos_rs_Tr3:"\<lbrakk>(0::nat) < r; 0 < s \<rbrakk> \<Longrightarrow>
                             inj_on (rtos r s) {i. i \<le> (r * s)}"
apply (frule rtos_inj [of "r" "s"], assumption+)
apply (simp add:inj_on_def [of _ "{i. i \<le> (r * s)}"])
 apply ((rule allI, rule impI)+, rule impI)
 apply (case_tac "x = r * s")
 apply (rule contrapos_pp, simp+)
 apply (frule not_sym)
 apply (frule mult_less_mono2[of "0" "s" "r"],
        simp only:mult.commute, simp only:mult_0_right)
 apply (cut_tac x = y and n = "r * s - Suc 0" in Nset_pre, simp+) 
 apply (frule_tac l = y in rtos_hom1[of "r" "s"], assumption+)
 apply (simp only: rtos_rs_Tr1) 
 apply (frule sym, thin_tac "r * s = rtos r s y", simp)
 apply (simp add:mult.commute[of "s" "r"])
 apply (simp add: not_less [symmetric, of "r * s" "r * s - Suc 0"])

apply (frule mult_less_mono2[of "0" "s" "r"],
       simp only:mult.commute, simp only:mult_0_right,
       cut_tac x = x in Nset_pre[of _ "r * s - Suc 0"], simp+) 
 apply (case_tac "y = r * s")
        apply (simp add: rtos_rs_Tr1)
 apply (frule_tac l = x in rtos_hom1[of "r" "s"], assumption+)       
       apply (simp add:mult.commute[of "s" "r"])
        apply (simp add: not_less [symmetric, of "r * s" "r * s - Suc 0"])
 
 apply (cut_tac x = y in Nset_pre[of _ "r * s - Suc 0"], simp+)
 apply (frule rtos_inj[of "r" "s"], assumption+)
  apply (simp add:inj_on_def)
done

lemma Qw_cmpser:"\<lbrakk>Group G; w_cmpser G (Suc n) f \<rbrakk> \<Longrightarrow> 
                               Gchain n (Qw_cmpser G f)" 
apply (simp add:Gchain_def)
apply (rule allI, rule impI)
 apply (simp  add:Qw_cmpser_def)
 apply (simp add:w_cmpser_def)
 apply (erule conjE)
 apply (simp add:d_gchain_def)
 apply (cut_tac c = l in subsetD[of "{i. i \<le> n}" "{i. i \<le> (Suc n)}"], 
        rule subsetI, simp, simp)
 apply (frule_tac H = "f l" in Group.Group_Gp[of "G"],
        frule_tac a = l in forall_spec, simp+)
 apply (frule_tac G = "Gp G (f l)" and N = "f (Suc l)" in Group.Group_Qg)
 apply blast apply assumption
done

definition
  wcsr_rfns :: "[_ , nat, nat \<Rightarrow> 'a set, nat] \<Rightarrow> (nat \<Rightarrow> 'a set) set" where
  "wcsr_rfns G r f s = {h. tw_cmpser G (s * r) h \<and> 
                                 (\<forall>i \<le> r. h (i * s) = f i)}"
      (** where f \<in> tw_cmpser G r **)
  (**  0-+-+-2-+-+-4-+-+-6  h 
      f 0   f 1   f 2   f 3  **)

definition
  trivial_rfn :: "[_ , nat, nat \<Rightarrow> 'a set, nat] \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "trivial_rfn G r f s k == if k < (s * r) then f (k div s) else f r"

lemma (in Group) rfn_tool8:"\<lbrakk>compseries G r f; 0 < r\<rbrakk> \<Longrightarrow> d_gchain G r f" 
apply (simp add:compseries_def tW_cmpser_def) 
apply (erule conjE)+
apply (simp add:tD_gchain_def) apply (erule conjE)+
apply (simp add:D_gchain_is_d_gchain)
done

lemma (in Group) rfn_tool16:"\<lbrakk>0 < r; 0 < s; i \<le> (s * r - Suc 0); 
 G \<guillemotright> f (i div s); (Gp G (f (i div s))) \<triangleright> f (Suc (i div s)); 
 (Gp G (f (i div s))) \<guillemotright> (f (i div s) \<inter> g (s - Suc 0))\<rbrakk>  \<Longrightarrow> 
 (Gp G ((f (Suc (i div s)) \<diamondop>\<^bsub>G\<^esub> (f (i div s) \<inter> g (s - Suc 0))))) \<triangleright> 
                                                   (f (Suc (i div s)))"
apply (rule ZassenhausTr4_1 [of "f (i div s)" "f (Suc (i div s))" "g (s - Suc 0)"], assumption+)
done

text\<open>Show existence of the trivial refinement. This is not necessary
to prove JHS\<close>

lemma rfn_tool30:"\<lbrakk>0 < r; 0 < s; l div s * s + s < s * r\<rbrakk> 
                \<Longrightarrow> Suc (l div s) < r"
apply (simp add:mult.commute[of "s" "r"])
apply (cut_tac add_mult_distrib[THEN sym, of "l div s" "s" "1"])
      apply (simp only:nat_mult_1)
apply (thin_tac "l div s * s + s = (l div s + 1) * s")
apply (cut_tac mult_less_cancel2[of "l div s + 1" "s" "r"])
       apply simp
done

lemma (in Group) simple_grouptr0:"\<lbrakk>G \<guillemotright> H; G \<triangleright> K; K \<subseteq> H; simple_Group (G / K)\<rbrakk>
  \<Longrightarrow> H = carrier G \<or> H = K" 
apply (simp add:simple_Group_def)
apply (frule subg_Qsubg[of "H" "K"], assumption+) 
apply (rotate_tac -1)
apply (frule in_set_with_P[of _ "carrier ((Gp G H) / K)"])
       apply simp
       apply (thin_tac "{N. G / K \<guillemotright> N } = {carrier (G / K), {\<one>\<^bsub>G / K\<^esub>}}")
 apply (erule disjE) 
 apply (frule sg_subset[of "H"])
 apply (frule equalityI[of "H" "carrier G"])
 apply (rule subsetI)
 apply (simp add:Qg_carrier)
 apply (frule nsg_sg[of "K"])
 apply (frule_tac a = x in rcs_in_set_rcs[of "K"], assumption+)
 apply (frule sym, thin_tac "carrier ((\<natural>H)/ K) = set_rcs G K", simp,
        thin_tac "set_rcs G K = carrier ((\<natural>H) / K)")
 apply (frule Group_Gp[of "H"], simp add:Group.Qg_carrier[of "Gp G H" "K"],
        simp add:set_rcs_def, erule bexE, simp add:Gp_carrier)

 apply (simp add:rcs_in_Gp[THEN sym])
 apply (frule_tac a = x in a_in_rcs[of "K"], assumption+, simp,
        thin_tac "K \<bullet> x = K \<bullet> a",
        thin_tac "G / K \<guillemotright> {C. \<exists>a\<in>H. C = K \<bullet> a}",
        simp add:rcs_def, erule bexE,
        frule_tac c = h in subsetD[of "K" "H"], assumption+)
 apply (frule_tac x = h and y = a in sg_mult_closed[of "H"], assumption+, simp)
 apply simp
 
apply (frule equalityI[THEN sym, of "K" "H"]) 
 apply (rule subsetI)
 apply (frule Group_Gp[of "H"], simp add:Group.Qg_carrier)
 apply (simp add:Qg_one)
 apply (frule nsg_sg[of "K"])
 apply (frule_tac a = x in Group.rcs_in_set_rcs[of "Gp G H" "K"]) 
  apply (simp add:sg_sg) apply (simp add:Gp_carrier)
  apply simp
  apply (frule_tac a = x in Group.rcs_fixed[of "Gp G H" "K"])
   apply (simp add:sg_sg) apply (simp add:Gp_carrier) apply assumption+
 apply simp
done

lemma (in Group) compser_nsg:"\<lbrakk>0 < n; compseries G n f; i \<le> (n - 1)\<rbrakk>
                  \<Longrightarrow>  Gp G (f i) \<triangleright> (f (Suc i))"
apply (simp add:compseries_def tW_cmpser_def)
done

lemma (in Group) compseriesTr5:"\<lbrakk>0 < n; compseries G n f; i \<le> (n - Suc 0)\<rbrakk>
          \<Longrightarrow> (f (Suc i)) \<subseteq>  (f i)"
apply (frule compseriesTr4[of "n" "f"])
apply (frule w_cmpser_is_d_gchain[of "n" "f"])
apply (simp add:d_gchain_def,
     cut_tac n_in_Nsetn[of "n"],
     frule_tac a = n in forall_spec, simp,
     thin_tac "\<forall>l \<le> n. G \<guillemotright> f l  \<and> (\<forall>l \<le> (n - Suc 0). f (Suc l) \<subseteq> f l)",
     erule conjE, blast)
done

lemma (in Group) refine_cmpserTr0:"\<lbrakk>0 < n; compseries G n f; i \<le> (n - 1);
        G \<guillemotright> H;  f (Suc i) \<subseteq> H \<and> H \<subseteq> f i\<rbrakk> \<Longrightarrow> H = f (Suc i) \<or> H = f i"
apply (frule compseriesTr0 [of "n" "f" "i"]) 
 apply (cut_tac lessI[of "n - Suc 0"], simp only:Suc_pred, simp)
 apply (frule Group_Gp [of "f i"]) 
 apply (erule conjE)
 apply (frule compseriesTr4[of "n" "f"])
 apply (frule w_cmpser_ns[of "n" "f" "i"], simp+) 
 apply (unfold compseries_def, frule conjunct2, fold compseries_def, simp)
 apply (frule_tac x = i in spec, 
        thin_tac "\<forall>i\<le>n - Suc 0. simple_Group ((\<natural>f i) / f (Suc i))",
        simp)
 apply (frule Group.simple_grouptr0 [of "Gp G (f i)" "H" "f (Suc i)"])
    apply (simp add:sg_sg) apply assumption+ 
 apply (simp add:Gp_carrier)
apply blast
done

lemma div_Tr4:"\<lbrakk> (0::nat) < r; 0 < s; j < s * r \<rbrakk> \<Longrightarrow> j div s * s + s \<le> r * s"
apply (frule div_Tr2 [of "r" "s" "j"], assumption+)
apply (frule mult_le_mono [of "j div s" "r - Suc 0" "s" "s"])
 apply simp
 apply (frule add_le_mono [of "j div s * s" "(r - Suc 0) * s" "s" "s"])
 apply simp
 apply (thin_tac "j div s * s \<le> (r - Suc 0) * s")
 apply (cut_tac add_mult_distrib[THEN sym, of "r - Suc 0" "s" "1"]) 
        apply (simp only:nat_mult_1)
apply simp
done

lemma (in Group) compseries_is_tW_cmpser:"\<lbrakk>0 < r; compseries G r f\<rbrakk> \<Longrightarrow>
        tW_cmpser G r f"
by (simp add:compseries_def)

lemma (in Group) compseries_is_td_gchain:"\<lbrakk>0 < r; compseries G r f\<rbrakk> \<Longrightarrow>
        td_gchain G r f"
apply (frule compseries_is_tW_cmpser, assumption+)
apply (simp add:tW_cmpser_def, erule conjE)
apply (thin_tac "\<forall>l\<le>(r - Suc 0). (\<natural>f l) \<triangleright> (f (Suc l))")
apply (simp add:tD_gchain_def, (erule conjE)+)
apply (frule D_gchain_is_d_gchain)
apply (simp add:td_gchain_def)
done

lemma (in Group) compseries_is_D_gchain:"\<lbrakk>0 < r; compseries G r f\<rbrakk> \<Longrightarrow>
             D_gchain G r f"
apply (frule compseriesTr1)
apply (frule tW_cmpser_is_W_cmpser)
apply (rule W_cmpser_is_D_gchain, assumption)
done

lemma divTr5:"\<lbrakk>0 < r; 0 < s; l < (r * s)\<rbrakk>  \<Longrightarrow>
                 l div s * s \<le> l \<and> l  \<le> (Suc (l div s)) * s"
apply (insert div_mult_mod_eq [THEN sym, of "l" "s"])
apply (rule conjI)
apply (insert le_add1 [of "l div s * s" "l mod s"])
apply simp
apply (frule mod_less_divisor [of "s" "l"])
 apply (frule less_imp_le [of "l mod s" "s"]) 
 apply (insert self_le [of "l div s * s"])
 apply (frule add_le_mono [of "l div s * s" "l div s * s" "l mod s" "s"])
 apply assumption+
apply (thin_tac "l div s * s \<le> l div s * s + l mod s")
apply (thin_tac "l div s * s \<le> l div s * s")
apply simp
done  

lemma (in Group) rfn_compseries_iMTr1:"\<lbrakk>0 < r; 0 < s; compseries G r f; 
h \<in> wcsr_rfns G r f s\<rbrakk> \<Longrightarrow>  f ` {i. i \<le> r} \<subseteq>  h ` {i. i \<le> (s * r)}"
apply (simp add:wcsr_rfns_def) apply (rule subsetI)
apply (simp add:image_def)
apply (auto del:equalityI)
apply (frule_tac i = xa in mult_le_mono [of _ "r" "s" "s"])
apply simp
apply (simp add:mult.commute [of "r" "s"])
apply (frule_tac a = xa in forall_spec, assumption,
       thin_tac "\<forall>i\<le>r. h (i * s) = f i")
apply (frule sym, thin_tac "h (xa * s) = f xa")
 apply (cut_tac a = xa in mult_mono[of _ r s s], simp, simp, simp, simp) 
 apply (simp only:mult.commute[of r s], blast) 
done

lemma rfn_compseries_iMTr2:"\<lbrakk>0 < r; 0 < s; xa < s * r \<rbrakk> \<Longrightarrow>
         xa div s * s \<le> r * s \<and> Suc (xa div s) * s \<le> r * s"
apply (frule div_Tr1 [of "r" "s" "xa"], assumption+)
 apply (simp add:less_imp_le)
apply (rule conjI)
 apply (simp add:mult_le_mono [of "xa div s" "r" "s" "s"])
apply (thin_tac "xa div s \<le> r")
apply (frule div_Tr2[of "r" "s" "xa"], assumption+)
 apply (thin_tac "xa < s * r")
 apply (frule le_less_trans [of "xa div s" "r - Suc 0" "r"])
 apply simp 
 apply (frule Suc_leI [of "xa div s" "r"])
 apply (rule mult_le_mono [of "Suc (xa div s)" "r" "s" "s"], assumption+)
apply simp
done

lemma (in Group) rfn_compseries_iMTr3:"\<lbrakk>0 < r; 0 < s; compseries G r f; 
      j \<le> r; \<forall>i \<le> r. h (i * s) = f i\<rbrakk> \<Longrightarrow>  h (j * s) = f j"
apply blast
done

lemma (in Group) rfn_compseries_iM:"\<lbrakk>0 < r; 0 < s; compseries G r f; 
      h \<in> wcsr_rfns G r f s\<rbrakk>  \<Longrightarrow> card (h `{i. i \<le> (s * r)}) = r + 1"
apply (frule compseries_is_D_gchain, assumption+)
apply (frule D_gchain1)
 apply simp
 apply (subst card_Collect_le_nat[THEN sym, of "r"])
 apply (subst card_image[THEN sym, of "f" "{i. i \<le> r}"], assumption+)
 apply (rule card_eq[of "h ` {i. i \<le> (s * r)}" "f ` {i. i \<le> r}"])
apply (frule rfn_compseries_iMTr1[of "r" "s" "f" "h"], assumption+)
apply (rule equalityI[of "h ` {i. i \<le> (s * r)}" "f ` {i. i \<le> r}"])
prefer 2 apply simp
apply (rule subsetI,
       thin_tac "f ` {i. i \<le> r} \<subseteq> h ` {i. i \<le> s * r}")
apply (frule_tac b = x and f = h and A = "{i. i \<le> (s * r)}" in mem_in_image3,
       erule bexE) apply (simp add:mult.commute[of "s" "r"])
apply (simp add:wcsr_rfns_def, (erule conjE)+)
apply (frule rfn_compseries_iMTr3[of "r" "s" "f" "r" "h"], assumption+,
       simp add:n_in_Nsetn, assumption+, subst image_def, simp)
 apply (case_tac "a = s * r", simp add:mult.commute[of "s" "r"],
        cut_tac n_in_Nsetn[of "r"], blast)
 apply (simp add:mult.commute[of "s" "r"])
 apply (frule_tac m = a and n = "r * s" in noteq_le_less, assumption+)
 apply (frule tw_cmpser_is_w_cmpser, frule w_cmpser_is_d_gchain)        
 apply (frule_tac xa = a in rfn_compseries_iMTr2[of "r" "s"], assumption+)
 apply (simp add:mult.commute)
 apply (erule conjE) 
 apply (frule_tac l = a in divTr5[of "r" "s"], assumption+) 
 apply (frule pos_mult_pos[of "r" "s"], assumption+) 
 apply (erule conjE,
        frule_tac l = "a div s * s" and j = a in d_gchainTr2[of "r * s" "h"],
        assumption+)
 apply (frule_tac l = a and j = "Suc (a div s) * s" in d_gchainTr2[of "r * s" 
       "h"], assumption+)
 apply (frule_tac i = a in rtos_hom0[of "r" "s"], assumption+)
 apply (rule less_le_diff)
 apply simp
 apply (frule_tac x = "a div s" and y = r in less_imp_le,
        frule_tac a = "a div s" in forall_spec, assumption,
        frule_tac a = "Suc (a div s)" in forall_spec)
 apply (cut_tac m = "Suc (a div s)" and k = s and n = r in mult_le_cancel2)
        apply simp
 apply (thin_tac "\<forall>i \<le> r. h (i * s) = f i") apply simp
 apply (cut_tac i = "a div s" and H = "h a"in refine_cmpserTr0[of "r" "f"],
        simp, assumption+,
        cut_tac x = "a div s" and n = r in less_le_diff, assumption, simp)
 apply (simp add:d_gchain_mem_sg[of "r * s" "h"])
 apply blast
 apply (erule disjE)
 apply (frule_tac m = "a div s" and n = r in Suc_leI, blast)
 apply (frule_tac x = "a div s" and y = r in less_imp_le, blast)
done

definition
  cmp_rfn :: "[_ , nat, nat \<Rightarrow> 'a set, nat, nat \<Rightarrow> 'a set] \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "cmp_rfn G r f s g = (\<lambda>i. (if i < s * r then  
      f (Suc (i div s)) \<diamondop>\<^bsub>G\<^esub> (f (i div s) \<inter> g (i mod s)) else {\<one>\<^bsub>G\<^esub>}))"

 (** refinement of compseries G r f by a compseries G s g **) 

lemma (in Group) cmp_rfn0:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g; 
 i \<le> (r - 1); j \<le> (s - 1)\<rbrakk> \<Longrightarrow> G \<guillemotright> f (Suc i) \<diamondop>\<^bsub>G\<^esub> ((f i ) \<inter> (g j))"
apply (rule ZassenhausTr2_1[of "f i" "f (Suc i)" "g j"], simp,
       rule compseriesTr0[of "r" "f" "i"], assumption+,
       frule_tac le_less_trans[of i "r - Suc 0" r], simp+)
 apply (rule compseriesTr0[of "r" "f" "Suc i"], assumption+, arith) 
 apply(rule compseriesTr0[of "s" "g" "j"], assumption+, simp)
apply (frule compseries_is_tW_cmpser[of "r" "f"], assumption+,
       simp add:tW_cmpser_def)
done

lemma (in Group) cmp_rfn1:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
  \<Longrightarrow> f (Suc 0) \<diamondop>\<^bsub>G\<^esub> ((f 0 ) \<inter> (g 0)) = carrier G"
apply (frule compseriesTr2 [of "r" "f"])
apply (frule compseriesTr2 [of "s" "g"])
apply (frule compseriesTr0 [of _ "f" "Suc 0"])
apply simp 
apply simp
apply (rule K_absorb_HK[of "f (Suc 0)" "carrier G"], assumption+,
       simp add:special_sg_G)
apply (rule sg_subset, assumption)
done

lemma (in Group) cmp_rfn2:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g;
           l \<le> (s * r)\<rbrakk>  \<Longrightarrow> G \<guillemotright> cmp_rfn G r f s g l"
 apply (simp add:cmp_rfn_def)
 apply (case_tac "l < s * r")
 apply simp
 apply (frule_tac i = "l div s" and j = "l mod s" in cmp_rfn0 [of "r" "s"],
                                                 assumption+)
 apply (simp add:div_Tr2)
 apply (frule_tac m = l in mod_less_divisor [of "s"])
 apply (frule_tac x = "l mod s" and n = s in less_le_diff)
 apply simp apply assumption 
apply simp
 apply (rule special_sg_e)
done

lemma (in Group) cmp_rfn3:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
 \<Longrightarrow> cmp_rfn G r f s g 0 = carrier G \<and> cmp_rfn G r f s g (s * r) = {\<one>}"
apply (rule conjI) 
 apply (simp add:cmp_rfn_def)
 apply (rule cmp_rfn1 [of "r" "s" "f" "g"], assumption+)
 apply (simp add:cmp_rfn_def)
done
 
lemma rfn_tool20:"\<lbrakk>(0::nat) < m; a = b * m + c; c < m \<rbrakk> \<Longrightarrow>  a mod m = c"
apply (simp add:add.commute)
done

lemma Suci_mod_s_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i mod s < s - Suc 0\<rbrakk>
        \<Longrightarrow> (Suc i) mod s = Suc (i mod s)"
apply (insert div_mult_mod_eq [of "i" "s", THEN sym])
apply (subgoal_tac "Suc i = i div s * s + Suc (i mod s)")
apply (subgoal_tac "Suc i mod s  = (i div s * s + Suc (i mod s)) mod s")
 apply (subgoal_tac "Suc (i mod s) < s")
 apply (frule_tac m = s and a = "Suc i" and b = "i div s" and c = "Suc (i mod s)" in rfn_tool20, assumption+)
 apply (subgoal_tac "Suc (i mod s) < Suc (s - Suc 0)")  apply simp
 apply (simp del:Suc_pred)
 apply simp+
done

lemma (in Group) inter_sgsTr1:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g; i < r * s\<rbrakk>  \<Longrightarrow> G \<guillemotright> f (i div s) \<inter> g (s - Suc 0)"
 apply (rule inter_sgs)
 apply (rule compseriesTr0, assumption+)  
 apply (frule less_imp_le [of "i" "r * s"])
 apply (frule div_Tr1 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult.commute, simp)
 apply (rule compseriesTr0, simp+) 
done

lemma (in Group) JHS_Tr0_2:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
\<Longrightarrow> \<forall>i \<le> (s * r - Suc 0). Gp G (cmp_rfn G r f s g i) \<triangleright> 
                                           cmp_rfn G r f s g (Suc i)"

apply (frule compseriesTr4 [of "r" "f"], frule compseriesTr4 [of "s" "g"])
apply (rule allI, rule impI)
 apply (frule pos_mult_pos [of "s" "r"], assumption+,
        frule_tac a = i in  rfn_tool11 [of "s * r"], assumption+,
        frule_tac l = i in div_Tr1 [of "r" "s"], assumption+,
        simp add:less_imp_le)
 apply (frule_tac x = "i div s" in mem_of_Nset [of _ "r"],
        thin_tac "i div s \<le> r", thin_tac "i \<le> s * r - Suc 0",
        frule_tac l = i in div_Tr2 [of "r" "s"], assumption+,
        frule_tac x = "i div s" in mem_of_Nset [of _ "r - Suc 0"],
        frule_tac a = "i div s" in rfn_tool11 [of "r"], assumption+,
        frule_tac m = "i div s" in Suc_leI [of _ "r"],
        frule_tac x = "Suc (i div s)" in mem_of_Nset [of _ "r"],
        thin_tac "i div s < r", thin_tac "Suc (i div s) \<le> r")
 apply (simp add:cmp_rfn_def)
 apply (case_tac "Suc i < s * r", simp,
         case_tac "i mod s = s - 1",
         cut_tac l = i in div_Tr3_1 [of "r" "s"],
         simp+,  
         cut_tac l = "Suc i" in div_Tr2 [of "r" "s"], simp+,
         cut_tac x = "Suc i div s" in mem_of_Nset [of _ "r - Suc 0"],
         simp,
         cut_tac a = "Suc i div s" in  rfn_tool11 [of "r"], simp+,
         cut_tac x = "Suc i div s" in less_mem_of_Nset [of _ "r"], simp,
         cut_tac m = "Suc i div s" in Suc_leI [of _ "r"], simp,
         frule_tac x = "Suc (Suc i div s)" in mem_of_Nset [of _ "r"],
         frule w_cmpser_is_d_gchain [of"r" "f"],
         frule_tac rfn_tool12_2 [of "s"], assumption+,
         thin_tac "i mod s = s - Suc 0",
         thin_tac "Suc i div s \<in> {i. i \<le> r}",
         thin_tac "Suc (Suc i div s) \<le> r")
  apply (simp,
         cut_tac l = "i div s" and j = "Suc (i div s)" in 
                       d_gchainTr2 [of "r" "f"], simp, assumption+,
         cut_tac x = "i div s" and y = "Suc (i div s)" and z = r in 
          less_trans, simp, assumption, simp add:less_imp_le, 
          simp add:less_imp_le, simp,
         cut_tac l = "Suc (i div s)" and j = "Suc (Suc (i div s))" in 
                       d_gchainTr2 [of "r" "f"], simp+,
         thin_tac "Suc i div s = Suc (i div s)", thin_tac "Suc i mod s = 0",
         cut_tac i = "i div s" in compseriesTr0 [of "r" "f"], assumption,
         simp, 
         cut_tac i = "Suc (i div s)" in compseriesTr0 [of  "r" "f"],
               assumption, simp add:less_imp_le,
         cut_tac i = "Suc (Suc (i div s))" in compseriesTr0 [of "r" "f"],
               assumption, simp)  
                                                            
 apply (subst compseriesTr2 [of "s" "g"], assumption, 
        frule_tac H = "f (i div s)" in sg_subset,
        frule_tac H = "f (Suc (i div s))" in sg_subset,
        frule_tac A = "f (Suc (i div s))" in Int_absorb2 [of _ "carrier G"], 
        simp,
        thin_tac "f (Suc (i div s)) \<inter> carrier G = f (Suc (i div s))",
        frule_tac H = "f (Suc (Suc (i div s)))" and K = "f (Suc (i div s))" in
        K_absorb_HK, assumption+,
        simp, 
        thin_tac "f (Suc (Suc (i div s))) \<diamondop>\<^bsub>G\<^esub> (f (Suc (i div s))) = 
                                                         f (Suc (i div s))")
apply (rule rfn_tool16 [of "r" "s" _], simp+,
       cut_tac x = "Suc i" and y = "s * r" and z = "Suc (s *r)" in 
       less_trans, assumption, simp,
       thin_tac "Suc i < s * r", simp)
apply (rule compser_nsg[of r f], simp+) 
 apply (rule_tac  H = "f (i div s) \<inter> g (s - Suc 0)" and K = "f (i div s)" in 
        sg_sg, assumption+,
        cut_tac i = i in inter_sgsTr1 [of r s f g], simp+,
        cut_tac x = i and y = "Suc i" and z = "s * r" in less_trans,
        simp+,
        cut_tac x = i and y = "Suc i" and z = "r * s" in less_trans,
        simp+,
        simp add:mult.commute, assumption+,
        simp add:Int_lower1)
 apply (frule_tac m = i in mod_less_divisor [of "s"],
        frule_tac x = "i mod s" in less_le_diff [of _ "s"],
        simp, 
        frule_tac m = "i mod s" in noteq_le_less [of _ "s - Suc 0"], 
        assumption+,
        thin_tac "i mod s \<noteq> s - Suc 0", thin_tac "i mod s \<le> s - Suc 0")
     apply (frule_tac x = "i mod s" and y = "s - Suc 0" and z = s in 
            less_trans, simp,
        frule_tac k = "i mod s" in nat_pos2 [of _ s],
        cut_tac l1 = i in div_Tr3_2 [THEN sym, of "r" "s"], simp+,
        frule_tac i = "i mod s" in compser_nsg [of "s" "g"], assumption+,
        simp, 
        frule_tac i = "Suc (i div s)" in compseriesTr0 [of "r" "f"], 
                  assumption+,
        frule_tac m = "i mod s" in Suc_mono [of _ "s - Suc 0"],
        simp only:Suc_pred)
 apply (frule_tac x = "Suc (i mod s)" in less_mem_of_Nset [of _ "s"],
        cut_tac i = "Suc (i mod s)" in compseriesTr0 [of "s" "g"], simp+,
        cut_tac H = "f (i div s)" and ?H1.0 = "f (Suc (i div s))" and 
        K = "g (i mod s)" and ?K1.0 = "g (Suc (i mod s))" in ZassenhausTr3,
        rule_tac i = "i div s" in compseriesTr0 [of "r" "f"], assumption+,
        frule_tac x = "i div s" and y = "r - Suc 0" and z = r in
        le_less_trans, simp, simp, assumption+,
        frule_tac i = "i mod s" in compseriesTr0 [of "s" "g"], 
        simp, simp, simp)
apply (rule_tac i = "i div s" in compser_nsg[of r f], simp+,
       cut_tac i = i in Suci_mod_s_2[of r s], simp+,
       cut_tac x = "Suc i" and y = "s * r" and z = "Suc (s *r)" in 
       less_trans, assumption, simp,
       thin_tac "Suc i < s * r", simp,
       frule_tac x = i and n = "s * r" in less_le_diff,
       simp add:mult.commute[of s r], simp+)
apply (cut_tac a = "i mod s" in rfn_tool11 [of "s"], simp+,
       frule_tac m = i in mod_less_divisor [of "s"],
       frule_tac x = "i mod s" in less_le_diff [of _ "s"], simp,
       rule special_nsg_e,
       cut_tac i = "i div s" and j = "i mod s" in cmp_rfn0[of r s f g],
       simp+)
done

lemma (in Group) cmp_rfn4:"\<lbrakk>0 < r; 0 < s; compseries G r f; 
      compseries G s g; l \<le> (s * r - Suc 0)\<rbrakk> \<Longrightarrow>
                 cmp_rfn G r f s g (Suc l) \<subseteq> cmp_rfn G r f s g l"
apply (frule JHS_Tr0_2 [of "r" "s" "f" "g"], assumption+)
apply (frule_tac a = l in forall_spec, simp,
       thin_tac "\<forall>i \<le> (s * r - Suc 0).
        (\<natural>(cmp_rfn G r f s g i)) \<triangleright> (cmp_rfn G r f s g (Suc i))")
apply (frule cmp_rfn2 [of "r" "s" "f" "g" "l"], assumption+,
       frule le_less_trans [of "l" "s * r - Suc 0" "s* r"], simp,
       simp add:less_imp_le)
apply (frule Group_Gp [of "cmp_rfn G r f s g l"],
       frule Group.nsg_subset [of "Gp G (cmp_rfn G r f s g l)"  ], 
       assumption+, simp add:Gp_carrier)
done

lemma (in Group) cmp_rfn5:"\<lbrakk>0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
    \<Longrightarrow> \<forall>i \<le> r. cmp_rfn G r f s g (i * s) = f i"
apply (rule allI, rule impI)
apply (simp add:cmp_rfn_def)
apply (case_tac "i < r", simp,
       frule_tac x = i in less_imp_le [of _ "r"],
       frule_tac x = i in mem_of_Nset[of _ "r"],
       frule_tac i = i in compseriesTr0 [of "r" "f"], assumption+,
       thin_tac "i \<le> r",
       frule_tac m = i in Suc_leI [of _ "r"],
       frule_tac x = "Suc i" in mem_of_Nset[of _ "r"],
       frule_tac i = "Suc i" in compseriesTr0 [of "r" "f"], assumption+)
apply (subst compseriesTr2 [of "s" "g"], assumption+,
       frule_tac H = "f i" in sg_subset,
       subst Int_absorb2, assumption+,
       frule rfn_tool8, assumption+, simp)
apply (cut_tac n = i in zero_less_Suc,
       frule_tac x = 0 and y = "Suc i" and z = r in less_le_trans, assumption+,
       frule_tac l = i and j = "Suc i" in d_gchainTr2 [of "r" "f"],
       frule compseries_is_D_gchain[of "r" "f"], assumption,
        rule D_gchain_is_d_gchain, assumption+,
       cut_tac x = i and y = "Suc i" and z = r in less_le_trans, simp+,
       rule_tac K = "f i" and H = "f (Suc i)" in  K_absorb_HK, assumption+,
       simp, frule compseries_is_td_gchain, assumption+,
       simp add:td_gchain_def) 
done

lemma (in Group) JHS_Tr0:"\<lbrakk>(0::nat) < r; 0 < s; compseries G r f; 
       compseries G s g\<rbrakk> \<Longrightarrow> cmp_rfn G r f s g \<in> wcsr_rfns G r f s"
apply (simp add:wcsr_rfns_def,
       frule cmp_rfn5 [of "r" "s" "f" "g"], assumption+,
       simp,
       thin_tac "\<forall>i\<le>r. cmp_rfn G r f s g (i * s) = f i")
apply (simp add:tw_cmpser_def, rule conjI)
prefer 2 apply (rule  JHS_Tr0_2 [of "r" "s" "f" "g"], assumption+)
apply (simp add:td_gchain_def, rule conjI)
prefer 2
apply (rule cmp_rfn3, assumption+) 
apply (simp add:d_gchain_def,
       rule allI, rule impI, rule conjI, rule cmp_rfn2, assumption+,
       rule allI, rule impI, rule cmp_rfn4, assumption+)
done

lemma rfn_tool17:"(a::nat) = b \<Longrightarrow> a - c = b - c"
by simp

lemma isom4b:"\<lbrakk>Group G; G \<triangleright> N; G \<guillemotright> H\<rbrakk> \<Longrightarrow> 
                  (Gp G (N \<diamondop>\<^bsub>G\<^esub> H) / N) \<cong> (Gp G H / (H \<inter> N))"
apply (frule isom4 [of "G" "N" "H"], assumption+)
apply (rule isomTr1)
 apply (simp add:Group.homom4_2)
 apply (frule Group.smult_sg_nsg[of "G" "H" "N"], assumption+)
 apply (simp add:Group.smult_commute_sg_nsg[THEN sym, of "G" "H" "N"])
apply (rule Group.homom4Tr1, assumption+)
done

lemma Suc_rtos_div_r_1:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; 
         Suc (rtos r s i) < r * s; i mod s = s - Suc 0; 
         i div s < r - Suc 0\<rbrakk> \<Longrightarrow>  Suc (rtos r s i) div r = i mod s"
apply (simp add:rtos_def,
       frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
apply simp
apply (subgoal_tac "Suc ((s - Suc 0) * r + i div s) div r = 
                      ((s - Suc 0) * r + Suc (i div s)) div r",
       simp del: add_Suc add_Suc_right)
apply (subgoal_tac "Suc (i div s) < Suc (r - Suc 0)")
apply simp_all
done

lemma Suc_rtos_mod_r_1:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s; i mod s = s - Suc 0; i  div s < r - Suc 0\<rbrakk>
         \<Longrightarrow> Suc (rtos r s i) mod r = Suc (i div s)"
apply (simp add:rtos_def)
done

lemma i_div_s_less:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s;
i mod s = s - Suc 0; Suc i < s * r \<rbrakk>  \<Longrightarrow> i div s < r - Suc 0"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
apply (frule_tac  r = r and s = s and l = i in div_Tr2, assumption+)
 apply (simp add:mult.commute) 
apply (rule contrapos_pp, simp+, 
        subgoal_tac "i div s = r - Suc 0",
        thin_tac "i div s = r - Suc 0")
apply (simp add:rtos_def,
       subgoal_tac "(s - Suc 0) * r + r = r * s", simp)
 apply (thin_tac "(s - Suc 0) * r + r < r * s")
 apply (simp add:mult.commute, simp add:diff_mult_distrib2)
apply simp
done

lemma rtos_mod_r_1:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; rtos r s i < r * s;
  i mod s = s - Suc 0 \<rbrakk>  \<Longrightarrow> rtos r s i mod r = i div s"
apply (simp add:rtos_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
 apply simp
 apply (rule rfn_tool20, assumption+, simp)
 apply (frule_tac r = r and s = s and l = i in div_Tr2, assumption+)
 apply (rule le_less_trans, assumption+, simp add:mult.commute)
 apply (rule le_less_trans, assumption+, simp)
done

lemma Suc_i_mod_s_0_1:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i mod s = s - Suc 0\<rbrakk>
        \<Longrightarrow> Suc i mod s = 0"
apply (insert div_mult_mod_eq [of "i" "s", THEN sym])
apply simp
 apply (thin_tac "i mod s = s - Suc 0")
apply (subgoal_tac "Suc i mod s = Suc (i div s * s + s - Suc 0) mod s")
 apply (thin_tac "i = i div s * s + s - Suc 0", simp del: add_Suc)
 apply (subgoal_tac "Suc (i div s * s + s - Suc 0) mod s = (i div s * s + s) mod s") 
 apply (simp del: add_Suc)
 apply (subgoal_tac "Suc (i div s * s + s - Suc 0) = i div s * s + s")
 apply (simp del: add_Suc)
apply (rule Suc_pred [of "i div s * s + s"], simp)
done

(* same as div_Tr3_2 *)
lemma Suci_div_s_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; i mod s < s - Suc 0\<rbrakk>
         \<Longrightarrow> Suc i div s = i div s"
apply (rule div_Tr3_2 [THEN sym], assumption+)
 apply simp
done

lemma rtos_i_mod_r_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0\<rbrakk> \<Longrightarrow> rtos r s i mod r = i div s"
apply (simp add:rtos_def)
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
apply simp
apply (frule_tac  r = r and s = s and l = i in div_Tr2, assumption+)
 apply (simp add:mult.commute)
apply (subgoal_tac "i div s < r") 
 apply (rule rfn_tool20, assumption+, simp)
 apply assumption
 apply (rule le_less_trans, assumption+, simp)
done

lemma Suc_rtos_i_mod_r_2:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; 
       i div s = r - Suc 0\<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = 0"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
apply (simp add:rtos_def)
done

lemma Suc_rtos_i_mod_r_3:"\<lbrakk>0 < r; 0 < s; i \<le> r * s - Suc 0; 
      i div s < r - Suc 0\<rbrakk> \<Longrightarrow> Suc (rtos r s i) mod r = Suc (i div s)"
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
apply (simp add:rtos_def)
done

lemma Suc_rtos_div_r_3:"\<lbrakk>0 < r; 0 < s; i mod s < s - Suc 0; i \<le> r * s - Suc 0; 
      Suc (rtos r s i) < r * s; i div s < r - Suc 0\<rbrakk> \<Longrightarrow> 
               Suc (rtos r s i) div r = i mod s"
apply (simp add:rtos_def) 
apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"]) 
apply simp
apply simp
apply (subst add_Suc_right[THEN sym, of "i mod s * r" "i div s"])
 apply (subst add.commute[of "i mod s * r" "Suc (i div s)"])
 apply (frule Suc_leI[of "i div s" "r - Suc 0"])
 apply (frule le_less_trans[of "Suc (i div s)" "r - Suc 0" "r"], simp)
 apply (subst div_mult_self1 [of "r" "Suc (i div s)" "i mod s"])
 apply auto
done

lemma r_s_div_s:"\<lbrakk>0 < r; 0 < s\<rbrakk> \<Longrightarrow> (r * s - Suc 0) div s = r - Suc 0"
apply (frule rfn_tool1_1 [of "s" "s - Suc 0" "r - Suc 0"]) 
 apply simp
 apply (simp add:diff_mult_distrib) 
done
 
lemma r_s_mod_s:"\<lbrakk>0 < r; 0 < s\<rbrakk> \<Longrightarrow> (r * s - Suc 0) mod s = s - Suc 0"
apply (frule rfn_tool20 [of "s" "(r - Suc 0) * s + (s - Suc 0)" "r - Suc 0"
        "s - Suc 0"], simp, simp)
apply (simp add:diff_mult_distrib)
done

lemma rtos_r_s:"\<lbrakk>0 < r; 0 < s\<rbrakk> \<Longrightarrow> rtos r s (r * s - Suc 0) = r * s - Suc 0"
apply (simp add:rtos_def)
apply (frule r_s_div_s [of "r" "s"], assumption+)
apply (frule r_s_mod_s [of "r" "s"], assumption+)
apply (simp, simp add:diff_mult_distrib, simp add:mult.commute)
done

lemma rtos_rs_1:"\<lbrakk> 0 < r; 0 < s; rtos r s i < r * s;
       \<not> Suc (rtos r s i) < r * s\<rbrakk> \<Longrightarrow> rtos r s i = r * s - Suc 0"
apply (frule pos_mult_pos [of "r" "s"], assumption+)
apply (frule less_le_diff [of "rtos r s i" "r * s"])
apply (simp add:nat_not_le_less[THEN sym, of "Suc (rtos r s i)" "r * s"])
done

lemma rtos_rs_i_rs:"\<lbrakk> 0 < r; 0 < s; i \<le> r * s - Suc 0; 
rtos r s i = r * s - Suc 0\<rbrakk> \<Longrightarrow>  i = r * s - Suc 0" 
apply (frule mem_of_Nset [of "i" "r * s - Suc 0"])     
apply (frule rtos_r_s [of "r" "s"], assumption+)
apply (frule rtos_inj[of "r" "s"], assumption+)
apply (cut_tac n_in_Nsetn[of "r * s - Suc 0"])
apply (simp add:inj_on_def)
done

lemma JHS_Tr1_1:"\<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk> \<Longrightarrow> f (Suc ((r * s - Suc 0) div s)) \<diamondop>\<^bsub>G\<^esub> (f ((r * s - Suc 0) div s) \<inter> g ((r * s - Suc 0) mod s)) = f (r - Suc 0) \<inter> g (s - Suc 0)"
apply (frule r_s_div_s [of "r" "s"], assumption+)
apply (frule r_s_mod_s [of "r" "s"], assumption+)
apply simp 
apply (subst Group.compseriesTr3 [of "G" "r" "f"], assumption+)
apply (frule Group.compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule Group.compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+)
 apply (simp add:less_mem_of_Nset)
apply (frule Group.inter_sgs [of "G" "f (r - (Suc 0))" "g (s - Suc 0)"], 
                                                          assumption+)
apply (rule Group.s_top_l_unit, assumption+)
done

lemma JHS_Tr1_2:"\<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
 k < r - Suc 0\<rbrakk> \<Longrightarrow> ((Gp G (f (Suc k) \<diamondop>\<^bsub>G\<^esub> (f k \<inter> g (s - Suc 0)))) / 
                               (f (Suc (Suc k)) \<diamondop>\<^bsub>G\<^esub> (f (Suc k) \<inter> g 0))) \<cong>
               ((Gp G (g s \<diamondop>\<^bsub>G\<^esub> (g (s - Suc 0) \<inter> f k))) /
                          (g s \<diamondop>\<^bsub>G\<^esub> (g (s - Suc 0) \<inter> f (Suc k))))"
apply (frule Group.compseriesTr0 [of "G" "r" "f" "k"], assumption+)
apply (frule less_trans [of "k" "r - Suc 0" "r"]) apply simp
apply simp 
apply (frule Suc_leI [of "k" "r - Suc 0"]) 
apply (frule le_less_trans [of "Suc k" "r - Suc 0" "r"]) apply simp
apply (frule Group.compseriesTr0 [of "G" "r" "f" "Suc k"], assumption+)
apply simp
 apply (thin_tac "Suc k \<le> r - Suc 0")
 apply (frule Suc_leI[of "Suc k" "r"])
apply (frule Group.compseriesTr0 [of "G" "r" "f" "Suc (Suc k)"], assumption+)
apply (frule Group.compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+)
apply simp
apply (subst Group.compseriesTr2 [of "G" "s" "g"], assumption+)
apply (subst Group.compseriesTr3 [of "G" "s" "g"], assumption+)
apply (subst Int_absorb2 [of "f (Suc k)" "carrier G"])
 apply (rule Group.sg_subset, assumption+) 
 apply (subst Group.K_absorb_HK[of "G" "f (Suc (Suc k))" "f (Suc k)"], assumption+) 
 apply (rule Group.compseriesTr5 [of "G" "r" "f" "Suc k"], assumption+)
 apply (frule Suc_leI [of "k" "r - Suc 0"])
 apply simp
apply (subst Group.s_top_l_unit[of "G" "g (s - Suc 0) \<inter> f k"], assumption+)
 apply (simp add:Group.inter_sgs)
apply (subst Group.compseriesTr3[of "G" "s" "g"], assumption+)
apply (subst Group.s_top_l_unit[of "G" "g (s - Suc 0) \<inter> f (Suc k)"], assumption+)
 apply (simp add:Group.inter_sgs)
apply (frule Group.Group_Gp [of "G" "f k"], assumption+) 
apply (frule Group.compser_nsg [of "G" "r" "f" "k"], assumption+)
apply (simp add:less_mem_of_Nset [of "k" "r - Suc 0"])
apply (frule isom4b [of "Gp G (f k)" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], 
                                                          assumption+)
apply (rule Group.sg_sg, assumption+)
 apply (rule Group.inter_sgs, assumption+)
 apply (simp add:Int_lower1)
 apply (frule Group.compseriesTr5[of "G" "r" "f" "k"], assumption+)
 apply simp
 apply (frule Group.s_top_induced[of "G" "f k" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], assumption+)
 apply (simp add:Int_lower1) apply simp 
  apply (thin_tac "f (Suc k) \<diamondop>\<^bsub>\<natural>\<^bsub>G\<^esub>(f k)\<^esub> (f k \<inter> g (s - Suc 0)) =
     f (Suc k) \<diamondop>\<^bsub>G\<^esub> (f k \<inter> g (s - Suc 0))")
  apply (frule Suc_pos [of "Suc k" "r"])
 apply (frule Group.cmp_rfn0 [of "G" "r" "s" "f" "g" "k" "s - Suc 0"], assumption+) 
 apply simp 
 apply simp
 apply (frule Group.sg_inc_set_mult[of "G" "f k" "f (Suc k)" "f k \<inter> g (s - Suc 0)"], assumption+) apply (simp add:Int_lower1)

 apply (simp add:Group.Gp_inherited [of "G" "f (Suc k) \<diamondop>\<^bsub>G\<^esub> (f k \<inter> g (s - Suc 0))" "f k"])
  apply (frule Group.inter_sgs [of "G" "f k" "g (s - Suc 0)"], assumption+)
apply (frule Group.Gp_inherited [of "G" "f k \<inter> g (s - Suc 0)" "f k"], assumption+)
apply (rule Int_lower1) apply simp
 apply (thin_tac "(Gp (Gp G (f k)) ((f k) \<inter> (g (s - Suc 0)))) =
                                        (Gp G ((f k) \<inter> (g (s - Suc 0))))")
 apply (thin_tac "f (Suc k) \<diamondop>\<^bsub>G\<^esub> f k \<inter> g (s - Suc 0) \<subseteq> f k")
 apply (thin_tac "G \<guillemotright> f (Suc k) \<diamondop>\<^bsub>G\<^esub> f k \<inter> g (s - Suc 0)")
 apply (simp add:Int_assoc [of "f k" "g (s - Suc 0)" "f (Suc k)"])
 apply (simp add:Int_commute [of "g (s - Suc 0)" "f (Suc k)"])
 apply (simp add:Int_assoc [of "f k" "f (Suc k)" "g (s - Suc 0)", THEN sym])
 apply (simp add:Int_absorb1[of "f (Suc k)" "f k"])
apply (simp add:Int_commute)
done

lemma JHS_Tr1_3:"\<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
       i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
       i mod s < s - Suc 0; Suc i div s \<le> r - Suc 0; i div s = r - Suc 0\<rbrakk>
    \<Longrightarrow> Group (Gp G (f r \<diamondop>\<^bsub>G\<^esub> (f (r - Suc 0) \<inter> g (i mod s))) /
        (f r \<diamondop>\<^bsub>G\<^esub> (f (r - Suc 0) \<inter> g (Suc (i mod s)))))"
apply (frule nat_eq_le[of "i div s" "r - Suc 0"])
apply (frule Group.compser_nsg [of "G" "r" "f" "i div s"], assumption+)
 apply simp
apply (frule Group.compser_nsg [of "G" "s" "g" "i mod s"], assumption+)
 apply simp
 apply (frule  Group.compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply simp 
 apply (frule  Group.compseriesTr0 [of "G" "r" "f" "r"], assumption+)
 apply simp 
 apply (frule  Group.compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply (simp add:less_imp_le)
 apply (frule  Group.compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
 apply (frule Suc_mono [of "i mod s" "s - (Suc 0)"],
        simp add:less_mem_of_Nset)
apply (frule Group.cmp_rfn0 [of "G" "r" "s" "f" "g" "i div s" "i mod s"], 
       assumption+, simp, simp) 
apply (frule  Group.ZassenhausTr3 [of "G" "f (r - Suc 0)" "f r" "g (i mod s)" 
       "g (Suc (i mod s))"], assumption+, simp, simp)
apply (cut_tac Group.Group_Gp [of "G" "f r \<diamondop>\<^bsub>G\<^esub> (f (r - Suc 0) \<inter> g (i mod s))"])
apply (rule Group.Group_Qg, assumption+)
apply simp
done

lemma JHS_Tr1_4:"\<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
       i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
       i mod s < s - Suc 0; Suc i div s \<le> r - Suc 0; i div s = r - Suc 0\<rbrakk> \<Longrightarrow> 
      Group (Gp G (g (Suc (i mod s)) \<diamondop>\<^bsub>G\<^esub> (g (i mod s) \<inter> f (r - Suc 0))) /
       (g (Suc (Suc (i mod s))) \<diamondop>\<^bsub>G\<^esub> (g (Suc (i mod s)) \<inter> f 0)))"
apply (subst Group.compseriesTr2 [of "G" "r" "f"], assumption+)
apply (frule Group.compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"], simp)
apply (frule Group.sg_subset [of "G" "g (Suc (i mod s))"], assumption+)
apply (subst Int_absorb2, assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"])
apply (frule less_mem_of_Nset [of "i mod s" "s - Suc 0"], simp)
apply (frule Suc_leI [of "Suc (i mod s)" "s"])
apply (frule Group.compseriesTr0 [of "G" "s" "g" "Suc (Suc (i mod s))"], 
             assumption+)
 apply (frule less_le_diff [of "Suc (i mod s)" "s"])
 apply (frule Suc_pos [of "Suc (i mod s)" "s"])
 apply (frule Group.compseriesTr5[of "G" "s" "g" "Suc (i mod s)"], assumption+)
 apply (subst Group.K_absorb_HK[of "G" "g (Suc (Suc (i mod s)))"
                                        "g (Suc (i mod s))"], assumption+)
apply (frule Group.compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply (frule mod_less_divisor [of "s" "i"], simp)
 apply (frule Group.cmp_rfn0 [of "G" "s" "r" "g" "f" "i mod s" "r - Suc 0"], 
        assumption+, simp, simp, simp)
 apply (cut_tac Group.compser_nsg [of "G" "s" "g" "i mod s"])
apply (frule Group.ZassenhausTr4_1 [of "G" "g (i mod s)" "g (Suc (i mod s))" 
                    "f (r - Suc 0)"], assumption+)
 apply (rule Group.sg_sg, assumption+)
 apply (rule Group.inter_sgs, assumption+)
 apply (rule Group.compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+)
 apply simp 
 apply (rule Int_lower1)
apply (rule Group.Group_Qg)
 apply (rule Group.Group_Gp, assumption+, simp+)
done

lemma JHS_Tr1_5:"\<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
      i \<le> s * r - Suc 0; Suc (rtos r s i) < s * r; Suc i < s * r;
      i mod s < s - Suc 0; i div s < r - Suc 0\<rbrakk>
 \<Longrightarrow> (Gp G (f (Suc (i div s)) \<diamondop>\<^bsub>G\<^esub> (f (i div s) \<inter> g (i mod s))) /
        (f (Suc (i div s)) \<diamondop>\<^bsub>G\<^esub> (f (i div s) \<inter> g (Suc (i mod s))))) \<cong>
     (Gp G (g (Suc (i mod s)) \<diamondop>\<^bsub>G\<^esub> (g (i mod s) \<inter> f (i div s))) /
       (g (Suc (Suc (rtos r s i) div r)) \<diamondop>\<^bsub>G\<^esub> 
              (g (Suc (rtos r s i) div r) \<inter> f (Suc (rtos r s i) mod r))))"
apply (frule Group.compseriesTr0 [of "G" "s" "g" "i mod s"], assumption+)
 apply simp 
apply (frule Group.compseriesTr0 [of "G" "s" "g" "Suc (i mod s)"], assumption+)
apply (frule Suc_mono [of "i mod s" "s - Suc 0"], simp)
apply (frule Group.compseriesTr0 [of "G" "r" "f" "i div s"], assumption+)
 apply (frule less_trans [of "i div s" "r - Suc 0" "r"], simp)
 apply simp
apply (frule Group.compseriesTr0 [of "G" "r" "f" "Suc (i div s)"], assumption+)
 apply (frule Suc_mono [of "i div s" "r - Suc 0"]) 
 apply simp 
 apply (frule Group.compser_nsg [of "G" "r" "f" "i div s"], assumption+)
 apply simp 
 apply (frule Group.compser_nsg [of "G" "s" "g" "i mod s"], assumption+, simp)
apply (subst Suc_rtos_i_mod_r_3 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute, assumption)
 apply (subst Suc_rtos_div_r_3 [of "r" "s" "i" ], assumption+)+
 apply (simp add:mult.commute)+
 apply (subst Suc_rtos_div_r_3[of "r" "s" "i"], assumption+)
apply (rule Zassenhaus [of "G" "f (i div s)" "f (Suc (i div s))" "g (i mod s)"
 "g (Suc (i mod s))"], assumption+)
done 

lemma JHS_Tr1_6:" \<lbrakk>Group G; 0 < r; 0 < s; compseries G r f; compseries G s g;
 i \<le> r * s - Suc 0; Suc (rtos r s i) < r * s\<rbrakk> \<Longrightarrow>
  ((Gp G (cmp_rfn G r f s g i)) / (cmp_rfn G r f s g (Suc i))) \<cong>
  ((Gp G (g (Suc (rtos r s i div r)) \<diamondop>\<^bsub>G\<^esub> 
      (g (rtos r s i div r) \<inter> f (rtos r s i mod r)))) /
      (g (Suc (Suc (rtos r s i) div r)) \<diamondop>\<^bsub>G\<^esub>
              (g (Suc (rtos r s i) div r) \<inter> f (Suc (rtos r s i) mod r))))"
apply (simp add:cmp_rfn_def)
 apply (frule le_less_trans [of "i" "r * s - Suc 0" "r * s"], simp)
 apply (simp add:mult.commute [of "r" "s"])
 apply (frule Suc_leI [of "i" "s * r"], thin_tac "i < s * r")
apply (case_tac "\<not> Suc i < s * r", simp)

 apply (frule rfn_tool17 [of "Suc i" "s * r" "Suc 0"])
 apply (thin_tac " Suc i = s * r")
 apply simp
 apply (frule rtos_r_s [of "r" "s"], assumption+) 
 apply (simp add:mult.commute [of "r" "s"])  (* !! ??? *) 
apply simp
apply (frule mod_less_divisor [of "s" "i"])
apply (frule less_le_diff [of "i mod s" "s"], thin_tac "i mod s < s")
 apply (case_tac "i mod s = s - Suc 0", simp)
 apply (frule_tac div_Tr2 [of "r" "s" "Suc i"], assumption+)
 apply (simp add:le_imp_less_or_eq)
 apply (subst div_Tr3_1[of "r" "s" "i"], assumption+, simp)
 apply (subst rtos_hom3 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult.commute)
 apply (subst rtos_hom3_1 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute)
apply (frule div_Tr3_1 [of "r" "s" "i"], assumption+, simp)
 apply (simp, thin_tac "Suc i div s = Suc (i div s)")
 apply (insert n_less_Suc [of "i div s"])
 apply (frule less_le_trans [of "i div s" "Suc (i div s)" "r - Suc 0"], 
                                                             assumption+)
 apply (subst Suc_rtos_div_r_1 [of "r" "s" "i"], assumption+) 
 apply (simp add:mult.commute[of "s" "r"])+ 
 apply (subst Suc_rtos_mod_r_1 [of "r" "s" "i"], assumption+)
 apply (subst Suc_i_mod_s_0_1 [of "r" "s" "i"], assumption+)
 apply (simp only:Suc_rtos_div_r_1 [of "r" "s" "i"])  
 apply (subst rtos_hom3[of "r" "s" "i"], assumption+, simp)

 apply (frule JHS_Tr1_2 [of "G" "r" "s" "f" "g" "i div s"], assumption+,
        simp)
apply (frule noteq_le_less [of "i mod s" "s - Suc 0"], assumption+)
 apply (thin_tac "i mod s \<le> s - Suc 0")
 apply (thin_tac "i mod s \<noteq> s - Suc 0")
 apply (frule div_Tr2 [of "r" "s" "Suc i"], assumption+,
        rule noteq_le_less, assumption+)
 apply (subst div_Tr3_2 [THEN sym, of "r" "s" "i"], assumption+)
 apply simp
 apply (subst rfn_tool12_1 [THEN sym, of "s" "i"], assumption+)
 apply simp
 apply (subst rtos_hom3 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute)
 apply (subst rtos_hom3_1 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute)
apply (case_tac "i div s = r - Suc 0")
apply (subst rtos_hom5 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute)
 apply assumption
 apply (subst rtos_hom7 [of "r" "s" "i"], assumption+)
 apply (simp add:mult.commute)
 apply (assumption, simp)
apply (frule JHS_Tr1_3 [of "G" "r" "s" "f" "g" "i"], assumption+,
       simp only:noteq_le_less,  assumption+)
apply (frule JHS_Tr1_4 [of "G" "r" "s" "f" "g" "i"], assumption+,
       simp only:noteq_le_less, assumption+)
 apply (subst rtos_hom3 [of "r" "s" "i"], assumption+,
        simp only:mult.commute[of "s" "r"])
 apply (subst rtos_hom5 [of "r" "s" "i"], assumption+,
        simp only:mult.commute[of "s" "r"],
               simp add:mem_of_Nset) 
apply (rule isomTr1, assumption+)
 apply (frule Suci_div_s_2[of "r" "s" "i"], assumption+,
        simp only:mult.commute, assumption)
 apply simp 
apply (frule Suci_div_s_2[of "r" "s" "i"], assumption+,
       simp only:mult.commute, assumption, simp)
apply (rule JHS_Tr1_2 [of "G" "s" "r" "g" "f" "i mod s"], assumption+)
apply (frule div_Tr2 [of "r" "s" "i"], assumption+)
 apply (rule le_less_trans [of "i" "s * r - Suc 0" "s * r"], assumption+)
 apply simp
apply (frule noteq_le_less [of "i div s" "r - Suc 0"], assumption+)
 apply (frule Suci_div_s_2[of "r" "s" "i"], assumption+,
        simp only:mult.commute[of "s" "r"], assumption, simp)
apply (frule JHS_Tr1_5[of "G" "r" "s" "f" "g" "i"], assumption+)
 apply (simp add:noteq_le_less[of "Suc i"], assumption+)
 apply (frule mem_of_Nset[of "i" "s*r - Suc 0"], 
                        simp add:mult.commute[of "s" "r"])
 apply (simp add:rtos_hom3 [of "r" "s" "i"])
done 

lemma JHS_Tr1:"\<lbrakk> Group G; 0 < r; 0 < s; compseries G r f; compseries G s g\<rbrakk>
\<Longrightarrow> isom_Gchains (r * s - 1) (rtos r s) (Qw_cmpser G (cmp_rfn G r f s g)) (Qw_cmpser G (cmp_rfn G s g r f))"
apply (simp add:isom_Gchains_def) 
 apply (rule allI, rule impI) 
 apply (frule pos_mult_pos [of "r" "s"], assumption+)
 apply (frule_tac b = "r * s" and a = i in rfn_tool11, assumption+)
apply (simp add:Qw_cmpser_def)
 apply (simp only:cmp_rfn_def [of "G" "s" "g"]) 
 apply (frule_tac l = i in rtos_hom1 [of "r" "s"], assumption+)
 apply (frule_tac x = "rtos r s i" and y = "s * r - Suc 0" and z = "s * r" in
          le_less_trans, simp)
 apply (simp add:mult.commute [of "s" "r"])
apply (case_tac "Suc (rtos r s i) < r * s", simp)
prefer 2 apply simp
 apply (frule_tac i = i in rtos_rs_1 [of "r" "s"], assumption+) 
 apply (frule_tac i = i in rtos_rs_i_rs [of "r" "s"], assumption+)
 apply (rule less_le_diff, assumption+)
 apply (simp add:cmp_rfn_def)
 apply (simp add:mult.commute)
apply (subst JHS_Tr1_1 [of "G" "r" "s" "f" "g"], assumption+)
apply (frule JHS_Tr1_1 [of "G" "s" "r" "g" "f"], assumption+)
 apply (simp add:mult.commute [of "r" "s"])
 apply (simp add:Int_commute) 
apply (frule Group.compseriesTr0 [of "G" "r" "f" "r - Suc 0"], assumption+,
       simp)
apply (frule Group.compseriesTr0 [of "G" "s" "g" "s - Suc 0"], assumption+,
       simp)
apply (frule Group.inter_sgs [of "G" "f (r - (Suc 0))" "g (s - Suc 0)"], 
                                                          assumption+)
apply (frule Group.special_sg_e [of "G"])
apply (frule Group.special_nsg_e [of "G" "f (r - Suc 0) \<inter> g (s - Suc 0)"], 
                                                        assumption+)
apply (frule Group.Group_Gp [of "G" "f (r - Suc 0) \<inter> g (s - Suc 0)"], assumption+)
apply (frule Group.Group_Qg[of "Gp G (f (r - Suc 0) \<inter> g (s - Suc 0))" "{\<one>\<^bsub>G\<^esub>}"],
       assumption+)
apply (simp add:isomTr0[of "(\<natural>\<^bsub>G\<^esub>(f (r - Suc 0) \<inter> g (s - Suc 0))) / {\<one>\<^bsub>G\<^esub>}"])
apply (rule JHS_Tr1_6, assumption+)
done
 
lemma abc_SucTr0:"\<lbrakk>(0::nat) < a; c \<le> b; a - Suc 0 = b - c\<rbrakk> \<Longrightarrow> a = (Suc b) - c"
apply (subgoal_tac "Suc 0 \<le> a")
apply (frule le_add_diff_inverse2 [of "Suc 0" "a", THEN sym])
apply auto 
done

lemma length_wcmpser0_0:"\<lbrakk>Group G; Ugp E; w_cmpser G (Suc 0) f\<rbrakk> \<Longrightarrow> 
       f ` {i. i \<le> (Suc 0)} = {f 0, f (Suc 0)}"
apply (simp add:Nset_1)
done

lemma length_wcmpser0_1:"\<lbrakk>Group G; Ugp E; w_cmpser G (Suc n) f; i\<in>{i. i \<le> n};
 (Qw_cmpser G f) i \<cong> E\<rbrakk> \<Longrightarrow> f i = f (Suc i)"
apply (subgoal_tac "0 < Suc n")
apply (frule Group.w_cmpser_gr [of "G" "Suc n" "f" "i"], assumption+) 
prefer 2 apply simp
apply (frule Group.w_cmpser_gr [of "G" "Suc n" "f" "Suc i"], simp+) 
apply (frule Group.w_cmpser_ns [of "G" "Suc n" "f" "i"], simp+)
apply (simp add:Qw_cmpser_def)
apply (rule QgrpUnit_3 [of "G" "E" "f i" "f (Suc i)"], assumption+, simp+)
done

lemma length_wcmpser0_2:"\<lbrakk>Group G; Ugp E; w_cmpser G (Suc n) f; i \<le> n;
 \<not> (Qw_cmpser G f) i \<cong> E\<rbrakk> \<Longrightarrow> f i \<noteq> f (Suc i)"       
apply (cut_tac zero_less_Suc[of "n"])
apply (frule Group.w_cmpser_gr [of "G" "Suc n" "f" "i"], assumption+) 
apply simp
apply (frule Group.w_cmpser_gr [of "G" "Suc n" "f" "Suc i"], assumption+) 
apply simp
apply (frule Group.w_cmpser_ns [of "G" "Suc n" "f" "i"], assumption+, simp)
apply (simp add:Qw_cmpser_def)
apply (rule QgrpUnit_4 [of "G" "E" "f i" "f (Suc i)"], assumption+)
done

lemma length_wcmpser0_3:"\<lbrakk>Group G; Ugp E; w_cmpser G (Suc (Suc n)) f;
  f (Suc n) \<noteq> f (Suc (Suc n))\<rbrakk> \<Longrightarrow> f (Suc (Suc n)) \<notin> f ` {i. i \<le> (Suc n)}"
apply (frule Group.w_cmpser_is_d_gchain, assumption+)
apply (thin_tac "w_cmpser G (Suc (Suc n)) f")
apply (rule contrapos_pp, simp+)
apply (frule Group.d_gchainTr2 [of "G" "Suc ((Suc n))" "f" "Suc n" "Suc (Suc n)"])
apply simp apply assumption+ apply simp+
apply (frule psubsetI [of "f (Suc (Suc n))" "f (Suc n)"])
apply (rule not_sym, assumption+) 
apply (thin_tac "f (Suc (Suc n)) \<subseteq> f (Suc n)")
apply (simp add:image_def)
apply (erule exE)
apply (cut_tac zero_less_Suc[of "Suc n"])
apply (frule_tac f = f and l = x in Group.d_gchainTr2 [of "G" "Suc ((Suc n))" 
                              _ _ "Suc (Suc n)"], assumption+)
 apply simp+
apply (frule_tac f = f and l = x in Group.d_gchainTr2 [of "G" "Suc (Suc n)" 
                              _ _ "Suc n"], simp+)
done

lemma length_wcmpser0_4:"\<lbrakk>Group G; Ugp E; w_cmpser G (Suc 0) f\<rbrakk> \<Longrightarrow>
  card (f ` {i. i \<le> Suc 0}) - 1 = Suc 0 - card {i. i = 0 \<and> 
                                                Qw_cmpser G f i \<cong> E}"
 (* card (f ` Nset (Suc 0)) - 1 =
           Suc 0 - card {i. i \<in> Nset 0 \<and> Qw_cmpser G f i \<cong> E}" *)
apply (auto simp add: length_wcmpser0_0 Collect_conv_if)
 apply (frule_tac n = 0 and f = f and i = 0 in length_wcmpser0_1 [of "G" "E"],         assumption+, simp+)
apply (frule_tac f = f and i = 0 in length_wcmpser0_2 [of "G" "E" "0"], 
       (assumption | simp)+)
done

lemma length_wcmpser0_5:" \<lbrakk>Group G; Ugp E; w_cmpser G (Suc (Suc n)) f; 
      w_cmpser G (Suc n) f;  
        card (f ` {i. i \<le> (Suc n)}) - 1 = Suc n - 
                     card {i. i \<le> n  \<and> Qw_cmpser G f i \<cong> E}; 
        Qw_cmpser G f (Suc n) \<cong> E\<rbrakk> \<Longrightarrow>
      card (f ` {i . i \<le> (Suc (Suc n))}) - 1 =
             Suc (Suc n) - card {i. i \<le> (Suc n) \<and> Qw_cmpser G f i \<cong> E}"
apply (frule_tac n = "Suc n" and f = f and i = "Suc n" in 
                            length_wcmpser0_1 [of "G" "E"], assumption+)
 apply (simp, assumption)
apply (subgoal_tac "f ` {i. i \<le> (Suc (Suc n))} = f ` {i. i \<le> (Suc n)}")
 apply simp
  prefer 2  apply (rule equalityI) 
  apply (simp add:image_def)
  apply (auto del:equalityI)
  apply (case_tac "xa = Suc (Suc n)", simp)  
  apply (thin_tac " xa = Suc (Suc n)", rotate_tac -2)
  apply (frule sym, thin_tac "f (Suc n) = f (Suc (Suc n))",
         simp, thin_tac "f (Suc (Suc n)) = f (Suc n)")
 apply (cut_tac n_in_Nsetn[of "Suc n"], blast)
  apply (frule_tac m = xa and n = "Suc (Suc n)" in noteq_le_less, assumption,
         frule_tac x = xa in Suc_less_le[of _ "Suc n"], blast)
apply (subgoal_tac "{i. i \<le> (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
              insert (Suc n) {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}")
 apply simp
apply fastforce
done

lemma length_wcmpser0_6:"\<lbrakk>Group G; w_cmpser G (Suc (Suc n)) f\<rbrakk> \<Longrightarrow> 
                                          0 < card (f ` {i. i \<le> (Suc n)})"
apply (insert finite_Collect_le_nat [of "Suc n"])
apply (frule finite_imageI [of "{i. i \<le> (Suc n)}" "f"])
apply (subgoal_tac "{f 0} \<subseteq> f ` {i. i \<le> (Suc n)}")
apply (frule card_mono [of "f ` {i. i \<le> (Suc n)}" "{f 0}"], assumption+)
apply (simp add:card1 [of "f 0"])
apply (rule subsetI, simp add:image_def)
apply (subgoal_tac "0 \<in> {i. i \<le> (Suc n)}", blast)
apply simp
done

lemma length_wcmpser0_7:"\<lbrakk>Group G; w_cmpser G (Suc (Suc n)) f\<rbrakk> \<Longrightarrow>
                     card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E} \<le> Suc n"
apply (insert finite_Collect_le_nat [of "n"])
apply (subgoal_tac "{i. i \<le> n \<and> Qw_cmpser G f i \<cong> E} \<subseteq> {i. i \<le> n}")
apply (frule card_mono [of "{i. i \<le> n}" "{i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}"])
 apply (assumption, simp)
apply (rule subsetI, simp add:CollectI)
done


lemma length_wcmpser0:"\<lbrakk>Group G; Ugp E\<rbrakk> \<Longrightarrow>\<forall>f. w_cmpser G (Suc n) f \<longrightarrow>  
card (f ` {i. i \<le> (Suc n)}) - 1 = (Suc  n) - (card {i. i \<le> n \<and> 
                                      ((Qw_cmpser G f) i \<cong> E)})"
apply (induct_tac n)  
 (*** n = 0 ***)
apply (rule allI) apply (rule impI)
apply (frule_tac f = f in length_wcmpser0_4[of G E], assumption+, simp)
  (**** n ****)
 apply (rule allI) apply (rule impI)
 apply (frule_tac n = "Suc n" and f = f in Group.w_cmpser_pre [of "G"], assumption+)
 apply (subgoal_tac "card (f ` {i. i \<le> (Suc n)}) - 1 =
                 Suc n - card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}")
 prefer 2 apply simp
 apply (thin_tac " \<forall>f. w_cmpser G (Suc n) f \<longrightarrow>
                 card (f ` {i. i \<le> (Suc n)}) - 1 =
                 Suc n - card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}")
apply (case_tac "Qw_cmpser G f (Suc n) \<cong> E")  
apply (rule length_wcmpser0_5, assumption+)
apply (frule_tac n = "Suc n" and f = f and i = "Suc n" in 
                            length_wcmpser0_2 [of "G" "E"], assumption+)
 apply simp  apply assumption
 apply (subgoal_tac "f ` {i. i \<le> (Suc (Suc n))} = 
                       insert (f (Suc (Suc n))) (f ` {i. i \<le> (Suc n)})")
 apply simp apply (thin_tac "f ` {i. i \<le> (Suc (Suc n))} =
             insert (f (Suc (Suc n))) (f ` {i. i \<le> (Suc n)})")
 apply (subgoal_tac "finite (f ` {i. i \<le> (Suc n)})")
 apply (subgoal_tac "f (Suc (Suc n)) \<notin> f ` {i. i \<le> (Suc n)}")
 apply (subst card_insert_disjoint, assumption) 
 apply assumption
 prefer 2  apply (rule length_wcmpser0_3, assumption+)
 prefer 2
  apply (subgoal_tac "finite {i. i \<le> (Suc n)}")
  apply (rule finite_imageI, assumption+, simp)
 prefer 2 
 apply (thin_tac " \<not> Qw_cmpser G f (Suc n) \<cong> E",
        thin_tac " w_cmpser G (Suc n) f",
        thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))")
 apply (subgoal_tac "{i. i \<le> (Suc (Suc n))} = {i. i\<le>(Suc n)} \<union> {Suc (Suc n)}")
 prefer 2 apply (rule_tac n = "Suc n" in Nset_un, simp)
 apply (subgoal_tac "card {i. i \<le> (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
                        card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}")
 apply simp 
 apply (thin_tac " card {i. i \<le> (Suc n) \<and> Qw_cmpser G f i \<cong> E} =
             card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}",
        thin_tac "\<not> Qw_cmpser G f (Suc n) \<cong> E",
        thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))",
        thin_tac "f (Suc (Suc n)) \<notin> f ` {i. i \<le> (Suc n)}")
 apply (frule_tac n = n and f = f in length_wcmpser0_6 [of "G"], assumption+,
        frule_tac n = n and f = f in length_wcmpser0_7 [of "G"], assumption+)
 apply (rule abc_SucTr0, assumption+)
apply (rule card_eq)
 apply (thin_tac "card (f ` {i. i \<le> (Suc n)}) - Suc 0 =
             Suc n - card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}",
        thin_tac "f (Suc n) \<noteq> f (Suc (Suc n))",
        thin_tac "f (Suc (Suc n)) \<notin> f ` {i. i \<le> (Suc n)}")
 apply (rule equalityI)
 apply (rule subsetI, simp add:CollectI, erule conjE)
 apply (case_tac "x = Suc n", simp, simp)
 apply (rule subsetI, simp add:CollectI)
done


lemma length_of_twcmpser:"\<lbrakk>Group G; Ugp E; tw_cmpser G (Suc n) f \<rbrakk> \<Longrightarrow> 
      length_twcmpser G (Suc n) f = 
                     (Suc n) - (card {i. i \<le> n \<and> ((Qw_cmpser G f) i \<cong> E)})"
apply (unfold length_twcmpser_def)
apply (insert length_wcmpser0 [of "G" "E" "n"])
apply (subgoal_tac "w_cmpser G (Suc n) f", rotate_tac -1,
       simp, simp, 
       thin_tac "\<forall>f. w_cmpser G (Suc n) f \<longrightarrow>
           card (f ` {i. i \<le> (Suc n)}) - Suc 0 =
           Suc n - card {i. i \<le> n \<and> Qw_cmpser G f i \<cong> E}")
 apply (simp add:tw_cmpser_def w_cmpser_def, erule conjE)
 apply (thin_tac "\<forall>i\<le> n. Gp G (f i) \<triangleright> f (Suc i)")
 apply (simp add:td_gchain_def)
done 

lemma JHS_1:"\<lbrakk>Group G; Ugp E; compseries G r f; compseries G s g; 0<r; 0 < s\<rbrakk>
 \<Longrightarrow> r =  r * s - card {i. i \<le> (r * s - Suc 0) \<and>
            Qw_cmpser G (cmp_rfn G r f s g) i \<cong> E}"
apply (frule_tac r = r and s = s and G = G and f = f and g = g in 
                   Group.JHS_Tr0, assumption+)
apply (simp add:wcsr_rfns_def, erule conjE)
apply (frule_tac length_of_twcmpser [of "G" "E" "r * s - Suc 0" 
        "cmp_rfn G r f s g"], assumption+, simp add:mult.commute)
apply (simp add:length_twcmpser_def)
apply (frule Group.rfn_compseries_iM [of "G" "r" "s" "f" "cmp_rfn G r f s g"], assumption+, rule Group.JHS_Tr0 [of "G" "r" "s" "f" "g"], assumption+)
apply (simp add:mult.commute [of "s" "r"])
done

lemma J_H_S:"\<lbrakk>Group G; Ugp E; compseries G r f; compseries G s g; 0<r;
               (0::nat)<s \<rbrakk>  \<Longrightarrow> r = s"
apply (frule JHS_1 [of "G" "E" "r" "f" "s" "g"], assumption+,
       frule JHS_1 [of "G" "E" "s" "g" "r" "f"], assumption+,
       frule JHS_Tr1 [of "G" "r" "s" "f" "g"], assumption+,
       frule Group.JHS_Tr0 [of "G" "r" "s" "f" "g"], assumption+,
       frule Group.JHS_Tr0 [of "G" "s" "r" "g" "f"], assumption+)
 apply (simp add:wcsr_rfns_def, (erule conjE)+,
       frule Group.tw_cmpser_is_w_cmpser [of "G" "s * r" "cmp_rfn G r f s g"],
                                                        assumption+,
       frule Qw_cmpser [of "G" "s * r - Suc 0" "cmp_rfn G r f s g"],
       simp add:pos_mult_pos [of "s" "r"])
 apply (frule Group.tw_cmpser_is_w_cmpser [of "G" "r * s" "cmp_rfn G s g r f"],
                                                        assumption+,
        frule Qw_cmpser [of "G" "r * s - Suc 0" "cmp_rfn G s g r f"],
        simp add:pos_mult_pos [of "r" "s"],
        simp add:mult.commute [of "s" "r"])
apply (frule isom_gch_units [of "E" "r * s - Suc 0" 
 "Qw_cmpser G (cmp_rfn G r f s g)" "Qw_cmpser G (cmp_rfn G s g r f)" 
                                               "rtos r s"], assumption+)
prefer 2 apply simp
apply (simp add:Gch_bridge_def)
apply (rule conjI) apply (rule allI, rule impI) 
 apply (frule_tac l = l in rtos_hom1 [of "r" "s"], assumption+,
        simp add:mult.commute [of "s" "r"])
apply (rule rtos_inj, assumption+)
done 

end
