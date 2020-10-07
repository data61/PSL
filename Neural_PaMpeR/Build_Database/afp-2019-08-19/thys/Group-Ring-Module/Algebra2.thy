(**                Algebra2  
                                  author Hidetsune Kobayashi
                                  Department of Mathematics
                                  Nihon University
                                  hikoba@math.cst.nihon-u.ac.jp
                                  May 3, 2004.
                                  April 6, 2007 (revised)

 chapter 2.  ordered set (continued)
   section 2    Pre elements 
   section 3    Transfinite induction
   section 4.   ordered_set2.  preliminary lemmas for Zorn's lemma 
   section 5.   Zorn's lemma

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem 
   section 1.    definition of a group 
   section 2.    subgroups
   section 3.    cosets
   section 4.    normal subgroups and quotient groups

  **)

theory Algebra2
imports Algebra1
begin

lemma (in Order) less_and_segment:"b \<in> carrier D \<Longrightarrow>
      (\<forall>a.((a \<prec> b \<and> a \<in> carrier D) \<longrightarrow> (Q a))) = 
      (\<forall>a\<in>carrier (Iod D (segment D b)).(Q a))"
apply (rule iffI)
 apply (rule ballI)
 apply (cut_tac segment_sub[of "b"], simp add:Iod_carrier,
        thin_tac "segment D b \<subseteq> carrier D",
        simp add:segment_def)
apply (rule allI, rule impI, erule conjE)
 apply (cut_tac segment_sub[of "b"], simp add:Iod_carrier,
        thin_tac "segment D b \<subseteq> carrier D",
        simp add:segment_def)
done

lemma (in Worder) Word_compare2:"\<lbrakk>Worder E; 
    \<not> (\<forall>a\<in>carrier D. \<exists>b\<in>carrier E. ord_equiv (Iod D (segment D a)) 
                                             (Iod E (segment E b)))\<rbrakk> \<Longrightarrow> 
       \<exists>c\<in>carrier D. ord_equiv (Iod D (segment D c))  E"
apply simp 
apply (frule bex_nonempty_set[of "carrier D"],
       frule nonempty_set_sub[of "carrier D" _],
       thin_tac "\<exists>a\<in>carrier D. \<forall>b\<in>carrier E.
           \<not> ord_equiv (Iod D (segment D a)) (Iod E (segment E b))")

apply  (insert ex_minimum,
      frule_tac a = "{x \<in> carrier D. \<forall>b\<in>carrier E.
        \<not> ord_equiv (Iod D (segment D x)) (Iod E (segment E b))}" in 
        forall_spec, simp,
      thin_tac "{x \<in> carrier D. \<forall>b\<in>carrier E.
       \<not> ord_equiv (Iod D (segment D x)) (Iod E (segment E b))} \<noteq> {}",
      thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)",
      erule exE)
 apply (frule_tac X = "{x \<in> carrier D. \<forall>b\<in>carrier E.
      \<not> ord_equiv (Iod D (segment D x)) (Iod E (segment E b))}" and a = x in 
       minimum_elem_mem, assumption, simp)
  apply (rename_tac d)
 apply (erule conjE, thin_tac "\<forall>b\<in>carrier E.
             \<not> ord_equiv (Iod D (segment D d)) (Iod E (segment E b))")
 apply (frule_tac d = d in less_minimum) apply simp

 apply (simp add:less_and_segment) 
 apply (cut_tac a = d in segment_Worder)
 apply (frule_tac D = "Iod D (segment D d)" in  Worder.well_ord_compare1 [of _ 
       "E"], assumption+)
 apply (auto simp add: minimum_elem_def Iod_segment_segment)
done

lemma (in Worder) Worder_equiv:"\<lbrakk>Worder E; 
      \<forall>a\<in>carrier D. \<exists>b\<in>carrier E.  ord_equiv (Iod D (segment D a)) 
             (Iod E (segment E b));  
      \<forall>c\<in>carrier E. \<exists>d\<in>carrier D.  ord_equiv (Iod E (segment E c)) 
                    (Iod D (segment D d))\<rbrakk> \<Longrightarrow> ord_equiv D E"
apply (frule well_ord_compare1 [of "E"], assumption+,
       erule disjE, assumption)
apply (erule bexE,
       insert Worder,
       frule_tac x = c in bspec, assumption+,
        thin_tac "\<forall>c\<in>carrier E. \<exists>d\<in>carrier D.
               ord_equiv (Iod E (segment E c)) (Iod D (segment D d))",
       erule bexE)

apply (cut_tac a = d in segment_Worder,
       cut_tac D = E and a = c in Worder.segment_Worder, assumption+,
       frule_tac D = "Iod D (segment D d)" in Worder.Order,
       frule_tac D = "Iod E (segment E c)" in Worder.Order,
       insert Order)
apply (frule_tac D = "D" and E = "Iod E (segment E c)" and 
       F = "Iod D (segment D d)" in Order.ord_equiv_trans, assumption+,
       frule_tac a = d in nonequiv_segment)
apply simp
done

lemma (in Worder) Worder_equiv1:"\<lbrakk>Worder E; \<not> ord_equiv D E\<rbrakk> \<Longrightarrow>
      \<not> ((\<forall>a\<in>carrier D. \<exists>b\<in>carrier E.  
         ord_equiv (Iod D (segment D a)) (Iod E (segment E b))) \<and> 
         (\<forall>c\<in>carrier E. \<exists>d\<in>carrier D.  
         ord_equiv (Iod E (segment E c)) (Iod D (segment D d))))"
apply (rule contrapos_pp, simp+) apply (erule conjE)
apply (frule Worder_equiv [of "E"], assumption+)
apply simp
done 

lemma (in Worder) Word_compare:"Worder E \<Longrightarrow>
 (\<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E) \<or> ord_equiv D E \<or> 
 (\<exists>b\<in>carrier E. ord_equiv D (Iod E (segment E b)))"
apply (frule Worder.Order[of "E"],
       case_tac "ord_equiv D E", simp)
 apply (frule Worder_equiv1 [of "E"], assumption+)
 apply simp
 apply (erule disjE) 
 apply (frule Word_compare2 [of  "E"], simp) 
 apply blast 
 apply (cut_tac  Worder.Word_compare2 [of "E" "D"])
apply (thin_tac "\<exists>c\<in>carrier E. \<forall>d\<in>carrier D.
           \<not> ord_equiv (Iod E (segment E c)) (Iod D (segment D d))")
 apply (erule bexE,
        cut_tac a = c in Worder.segment_Worder[of "E"], assumption+, 
        frule_tac D = "Iod E (segment E c)" in Worder.Order,
        insert Order,
        frule_tac D = "Iod E (segment E c)" and E = D in Order.ord_equiv_sym,
        assumption+, blast)
 apply assumption apply (simp add:Worder)
 apply simp
done
      
lemma (in Worder) Word_compareTr1:"\<lbrakk>Worder E;
      \<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E; ord_equiv D E \<rbrakk> \<Longrightarrow> 
     False"
apply (erule bexE,
       cut_tac a = a in segment_Worder,
       frule_tac D = E in Worder.Order,
       frule_tac D = "Iod D (segment D a)" in Worder.Order,
       frule_tac D = "Iod D (segment D a)" and E = E in Order.ord_equiv_sym,
       assumption+)
apply (insert Order,
       frule_tac D = D and E = E and F = "Iod D (segment D a)" in 
       Order.ord_equiv_trans, assumption+)
 apply (frule_tac a = a in nonequiv_segment, simp)
done  

lemma (in Worder) Word_compareTr2:"\<lbrakk>Worder E; ord_equiv D E; 
      \<exists>b\<in>carrier E. ord_equiv D (Iod E (segment E b))\<rbrakk> \<Longrightarrow> False"
apply (erule bexE)
apply (cut_tac a = b in Worder.segment_Worder [of "E"], assumption+)
apply (cut_tac Worder,
       frule Worder.Order[of "E"])
apply (frule_tac D = "Iod E (segment E b)" in Worder.Order)
apply (frule_tac E = E in ord_equiv_sym, assumption)
apply (meson Worder Worder.Word_compareTr1 ord_equiv_sym)
done

lemma (in Worder) Word_compareTr3:"\<lbrakk>Worder E; 
      \<exists>b\<in>carrier E. ord_equiv D (Iod E (segment E b)); 
      \<exists>a\<in>carrier D. ord_equiv (Iod D (segment D a)) E\<rbrakk> \<Longrightarrow> False"  
apply (erule bexE)+
 apply (simp add:ord_equiv_def[of "D"], erule exE)
 (** ord_isom_segment_segment **)
 apply (frule Worder.Torder[of "E"])
 apply (cut_tac a = b in Worder.segment_Worder [of "E"], assumption+,
        frule_tac D = "Iod E (segment E b)" in Worder.Torder,
        frule_tac D = "Iod E (segment E b)" in Worder.Order)
 apply (frule_tac E = "Iod E (segment E b)" and f = f and a = a in 
        ord_isom_segment_segment, assumption+) 
 apply (frule_tac f = f and a = a and E = "Iod E (segment E b)" in 
        ord_isom_mem, assumption+,
        frule Worder.Order[of "E"], 
        frule_tac b = b and a = "f a" in Order.Iod_segment_segment[of "E"],
        assumption+, simp,
        thin_tac "Iod (Iod E (segment E b)) (segment (Iod E (segment E b)) 
        (f a)) =  Iod E (segment E (f a))")

 apply (frule_tac D = "E" and a = b in Order.segment_sub)
        apply (simp add:Order.Iod_carrier[of "E"])
        apply (frule_tac c = "f a" and A = "segment E b" and B = "carrier E"
               in subsetD, assumption+)
  apply (cut_tac a = a in segment_Worder,
         frule_tac D = "Iod D (segment D a)" in Worder.Order,
         cut_tac a = "f a" in Worder.segment_Worder [of "E"], assumption+,
         frule_tac D = "Iod E (segment E (f a))" in Worder.Order) 
apply (
         frule_tac D = "Iod D (segment D a)" and E = "Iod E (segment E (f a))" in Order.ord_equiv, assumption, simp)
 apply (frule_tac D = "Iod D (segment D a)" and E = E in 
                                            Order.ord_equiv_sym, assumption+)
 apply (frule_tac D = E and E = "Iod D (segment D a)" and 
        F = "Iod E (segment E (f a))" in Order.ord_equiv_trans, assumption+)

 apply (simp add:Worder.nonequiv_segment[of "E"])
done 

lemma (in Worder) subset_equiv_segment:"S \<subseteq> carrier D \<Longrightarrow> 
      ord_equiv D (Iod D S) \<or> 
      (\<exists>a\<in>carrier D. ord_equiv (Iod D S) (Iod D (segment D a)))"
apply (frule subset_Worder [of "S"])
 apply (frule Word_compare [of "Iod D S"])

 apply (erule disjE)
 apply (erule bexE)
 apply (cut_tac a = a in segment_Worder,
        frule_tac D = "Iod D (segment D a)" in Worder.Order,
        frule Worder.Order[of "Iod D S"],
        frule_tac D = "Iod D (segment D a)" in Order.ord_equiv_sym[of _ 
                 "Iod D S"], assumption+, blast)

apply (erule disjE) apply simp
 apply (erule bexE)
 apply (frule Worder.Order[of "Iod D S"],
        frule_tac D = "Iod D S" and a = b in Order.segment_sub)
 apply (frule_tac S = "segment (Iod D S) b" in Order.Iod_sub_sub[of "Iod D S" _ "S"])
 apply (simp add:Iod_carrier) apply (simp add:Iod_carrier)
 apply (simp add:Iod_sub_sub[of "S" "S"])
 apply (simp add:Iod_carrier)
 apply (frule_tac S = "segment (Iod D S) b" in Iod_sub_sub[of _ "S"],
         assumption+, simp,
        thin_tac "Iod (Iod D S) (segment (Iod D S) b) = 
                                          Iod D (segment (Iod D S) b)")
 (** to_subset **)
 apply (simp add:ord_equiv_def, erule exE)
 apply (frule_tac A = "segment (Iod D S) b" and B = S and C = "carrier D" in
         subset_trans, assumption+,
        frule_tac c = b in subsetD[of "S" "carrier D"], assumption+)
 apply (frule_tac T = "segment (Iod D S) b" and f = f in to_subset,
         assumption+,
        frule_tac a = b in forall_spec, assumption, 
        thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow> a \<preceq> f a",
        frule_tac T = "segment (Iod D S) b" in Iod_Order,
        cut_tac D = "Iod D S" and a = b in Worder.segment_Worder) 
 apply (simp add:Iod_carrier) 
 apply (frule_tac S = "segment (Iod D S) b" in Iod_sub_sub[of _ "S"],
         assumption+, simp,
        thin_tac "Iod (Iod D S) (segment (Iod D S) b) = 
                                          Iod D (segment (Iod D S) b)")
 apply (insert Order,
        frule_tac E = "Iod D (segment (Iod D S) b)" and f = f and a = b in 
        ord_isom_mem, assumption+,
        simp add:Iod_carrier,
        frule_tac c = "f b" and A = "segment (Iod D S) b" in 
               subsetD[of _ "S"], assumption+,
        simp add:segment_def[of "Iod D S"],
        simp add:Iod_carrier,
        simp add:Iod_less)
 apply (frule_tac c = b in subsetD[of "S" "carrier D"], assumption+,
        frule_tac c = "f b" in subsetD[of "S" "carrier D"], assumption+,
        frule_tac a1 = "f b" and b1 = b in not_less_le[THEN sym], assumption+)
 apply simp
done

definition
  ordinal_number :: "'a Order  \<Rightarrow> 'a Order set" where
  "ordinal_number S = {X. Worder X \<and> ord_equiv X S}"

definition
  ODnums :: "'a Order set set" where
  "ODnums = {X. \<exists>S. Worder S \<and> X = ordinal_number S}"

definition
  ODord :: "['a Order set, 'a Order set] \<Rightarrow> bool" (infix "\<sqsubset>" 60) where
  "X \<sqsubset> Y \<longleftrightarrow> (\<exists>x \<in> X. \<exists>y \<in> Y. (\<exists>c\<in>carrier y. ord_equiv x (Iod y (segment y c))))"

definition
  ODord_le :: "['a Order set, 'a Order set] \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) where
  "X \<sqsubseteq> Y \<longleftrightarrow> X = Y \<or> ODord X Y"

definition
  ODrel :: "((('a Order) set) * (('a Order) set)) set" where
  "ODrel = {Z. Z \<in> ODnums \<times> ODnums \<and> ODord_le (fst Z) (snd Z)}" 

definition
  ODnods :: "('a Order set) Order" where
  "ODnods = \<lparr>carrier = ODnums, rel = ODrel \<rparr>"

lemma Worder_ord_equivTr:"\<lbrakk>Worder S; Worder T\<rbrakk> \<Longrightarrow>
       ord_equiv S T = (\<exists>f. ord_isom S T f)"
by (frule Worder.Order[of "S"], frule Worder.Order[of "T"],
    simp add:ord_equiv_def)

lemma Worder_ord_isom_mem:"\<lbrakk>Worder S; Worder T; ord_isom S T f; a \<in> carrier S\<rbrakk>
     \<Longrightarrow> f a \<in> carrier T"
by (frule Worder.Order[of "S"], frule Worder.Order[of "T"],
    simp add:Order.ord_isom_mem)

lemma Worder_refl:"Worder S \<Longrightarrow> ord_equiv S S"
apply (frule_tac Worder.Order [of "S"])
apply (rule Order.ord_equiv_reflex [of "S"], assumption+)
done

lemma Worder_sym:"\<lbrakk>Worder S; Worder T; ord_equiv S T \<rbrakk> \<Longrightarrow> ord_equiv T S"
apply (frule_tac Worder.Order [of "S"])
apply (frule_tac Worder.Order [of "T"])
apply (rule Order.ord_equiv_sym [of "S" "T"], assumption+)
done

lemma Worder_trans:"\<lbrakk>Worder S; Worder T; Worder U; ord_equiv S T; ord_equiv T U\<rbrakk> \<Longrightarrow> ord_equiv S U" 
apply (frule Worder.Order [of "S"],
       frule Worder.Order [of "T"],
       frule Worder.Order [of "U"])
apply (rule Order.ord_equiv_trans [of "S" "T" "U"], assumption+)
done  

lemma ordinal_inc_self:"Worder S \<Longrightarrow> S \<in> ordinal_number S"
by (simp add:ordinal_number_def, simp add:Worder_refl)

lemma ordinal_number_eq:"\<lbrakk>Worder D; Worder E\<rbrakk> \<Longrightarrow>
               (ord_equiv D E) = (ordinal_number D = ordinal_number E)"
apply (rule iffI)
 apply (simp add:ordinal_number_def)
 apply (rule equalityI)
 apply (rule subsetI) apply simp apply (erule conjE)
 apply (rule_tac S = x and T = D and U = E in Worder_trans,
                       assumption+)
 apply (rule subsetI, simp, erule conjE)
apply (rule_tac S = x and T = E and U = D in Worder_trans,
                       assumption+)  
 apply (rule Worder_sym, assumption+)
apply (simp add:ordinal_number_def)
apply (frule Worder_refl[of "D"],
       frule Worder_refl[of "E"])
apply blast
done

lemma mem_ordinal_number_equiv:"\<lbrakk>Worder D; 
           X \<in> ordinal_number D\<rbrakk> \<Longrightarrow> ord_equiv X D"
by (simp add:ordinal_number_def)

lemma mem_ordinal_number_Worder:"\<lbrakk>Worder D; 
           X \<in> ordinal_number D\<rbrakk> \<Longrightarrow> Worder X"
by (simp add:ordinal_number_def)

lemma mem_ordinal_number_Worder1:"\<lbrakk>x \<in> ODnums; X \<in> x\<rbrakk> \<Longrightarrow> Worder X"
apply (simp add:ODnums_def, erule exE, erule conjE, simp)
apply (rule mem_ordinal_number_Worder, assumption+)
done

lemma mem_ODnums_nonempty:"X \<in> ODnums \<Longrightarrow> \<exists>x. x \<in> X"
apply (simp add:ODnums_def, simp add:ordinal_number_def,
       erule exE, erule conjE)
apply (frule_tac S = S in Worder_refl, blast)
done

lemma carr_ODnods:"carrier ODnods = ODnums"
by (simp add:ODnods_def)

lemma ordinal_number_mem_carrier_ODnods:
     "Worder D \<Longrightarrow> ordinal_number D \<in> carrier ODnods"
by (simp add:ODnods_def ODnums_def, blast)

lemma ordinal_number_mem_ODnums: 
      "Worder D \<Longrightarrow> ordinal_number D \<in> ODnums"
by (simp add:ODnums_def, blast)

lemma ODordTr1:" \<lbrakk>Worder D; Worder E\<rbrakk> \<Longrightarrow> 
       (ODord (ordinal_number D) (ordinal_number E)) =
       (\<exists>b\<in> carrier E. ord_equiv D (Iod E (segment E b)))"
apply (rule iffI)
 apply (simp add:ODord_def)
 apply ((erule bexE)+, simp add:ordinal_number_def, (erule conjE)+)
 apply (rename_tac X Y c)

apply (frule_tac S = Y and T = E in Worder_ord_equivTr, assumption,
       simp, erule exE)
apply (frule_tac D = Y in Worder.Order,
       frule_tac D = E in Worder.Order,
       frule_tac D = Y and E = E and f = f and a = c in 
                 Order.ord_isom_segment_segment, assumption+,
       frule_tac S = Y and T = E and f = f and a = c in 
                 Worder_ord_isom_mem, assumption+)
apply (cut_tac D = Y and a = c in Worder.segment_Worder, assumption,
       cut_tac D = E and a = "f c" in Worder.segment_Worder, assumption)
apply (frule_tac S1 = "Iod Y (segment Y c)" and T1 = "Iod E (segment E (f c))" 
       in Worder_ord_equivTr[THEN sym], assumption+)
apply (frule_tac S = X and T = D in Worder_sym, assumption+,
       thin_tac "ord_equiv X D",
       frule_tac S = D and T = X and U = "Iod Y (segment Y c)" in 
                 Worder_trans, assumption+,
       frule_tac S = D and T = "Iod Y (segment Y c)" and 
           U = "Iod E (segment E (f c))" in Worder_trans, assumption+)
apply blast apply blast 

apply (simp add:ODord_def)  
apply (frule ordinal_inc_self[of "D"],
       frule ordinal_inc_self[of "E"], blast)
done

lemma ODord:" \<lbrakk>Worder D; d \<in> carrier D\<rbrakk> \<Longrightarrow> 
       ODord (ordinal_number (Iod D (segment D d))) (ordinal_number D)"
apply (cut_tac Worder.segment_Worder[of "D" "d"], 
       subst ODordTr1[of "Iod D (segment D d)" "D"], assumption+,
       frule Worder_refl[of "Iod D (segment D d)"], blast, assumption)
done

lemma ord_less_ODord:"\<lbrakk>Worder D; c \<in> carrier D; d \<in> carrier D; 
           a = ordinal_number (Iod D (segment D c));
           b = ordinal_number (Iod D (segment D d))\<rbrakk> \<Longrightarrow>
                         c \<prec>\<^bsub>D\<^esub> d =  a \<sqsubset> b"
apply (rule iffI)
apply (frule Worder.Order[of "D"])
apply (simp add:Order.segment_inc) 
apply (frule Order.Iod_carr_segment[THEN sym, of "D" "d"],
       frule eq_set_inc[of "c" "segment D d" "carrier (Iod D (segment D d))"],
       assumption+,
       thin_tac "segment D d = carrier (Iod D (segment D d))",
       thin_tac "c \<in> segment D d")
apply (cut_tac Worder.segment_Worder[of "D" "d"], 
       frule ODord[of "Iod D (segment D d)" "c"], assumption+,
       simp add:Order.Iod_segment_segment, assumption)

apply simp
 apply (frule Worder.segment_Worder[of D c],
        frule Worder.segment_Worder[of D d])
 apply (simp add:ODordTr1[of "Iod D (segment D c)" "Iod D (segment D d)"],
        thin_tac "a = ordinal_number (Iod D (segment D c))",
        thin_tac "b = ordinal_number (Iod D (segment D d))")
 apply (erule bexE)
 apply (frule Worder.Order[of D])

 apply (simp add:Order.Iod_segment_segment)
 apply (simp add:Order.Iod_carr_segment,
        frule Order.segment_sub[of D d],
        frule_tac c = b in subsetD[of "segment D d" "carrier D"], assumption+)
 apply (frule_tac b = b in Worder.segment_unique[of D c], assumption+, simp)
 apply (simp add:Order.segment_inc[THEN sym])
done

lemma ODord_le_ref:"\<lbrakk>X \<in> ODnums; Y \<in> ODnums; ODord_le X Y; Y \<sqsubseteq> X \<rbrakk> \<Longrightarrow>
                               X = Y"
apply (simp add:ODnums_def)
 apply ((erule exE)+, (erule conjE)+, rename_tac S T)
 apply (simp add:ODord_le_def)
 apply (erule disjE, simp)
 apply (erule disjE, simp)
 
 apply (simp add:ODordTr1)
 apply (frule_tac D = T and E = S in Worder.Word_compareTr3, assumption+)
 apply (erule bexE)
 apply (frule_tac D = T and a = b in Worder.segment_Worder)
 apply (frule_tac S = S and T = "Iod T (segment T b)" in Worder_sym,
         assumption+) apply blast
 
 apply simp
done

lemma ODord_le_trans:"\<lbrakk>X \<in> ODnums; Y \<in> ODnums; Z \<in> ODnums; X \<sqsubseteq> Y; Y \<sqsubseteq> Z \<rbrakk>
                     \<Longrightarrow>  X \<sqsubseteq> Z" 
apply (simp add:ODord_le_def)
 apply (erule disjE, simp)
 apply (erule disjE, simp)

 apply (simp add:ODnums_def, (erule exE)+, (erule conjE)+)
 apply (rename_tac A B C, simp)
 apply (simp add:ODordTr1,
        thin_tac "X = ordinal_number A",
        thin_tac "Y = ordinal_number B",
        thin_tac "Z = ordinal_number C")
 apply (erule bexE)+

 (* going to apply ord_isom_segment_segment *)
 apply (frule_tac D = B in Worder.Order,
        frule_tac D = C in Worder.Order,
        frule_tac D = C and a = ba in Worder.segment_Worder,
        frule_tac D = "Iod C (segment C ba)" in Worder.Order,
        frule_tac D = B and E = "Iod C (segment C ba)" in 
                  Order.ord_equiv_isom, assumption+, erule exE)
 apply (frule_tac D = B and E = "Iod C (segment C ba)" and f = f in 
         Order.ord_isom_segment_segment, assumption+,
        frule_tac D = B and E = "Iod C (segment C ba)" and f = f and a = b in
         Order.ord_isom_mem, assumption+) 
        (** ord_isom_segment_segment applied **)
 
 apply (simp add:Order.Iod_segment_segment) 
 apply (frule_tac D = B and a = b in Worder.segment_Worder,
        frule_tac D = "Iod B (segment B b)" in Worder.Order,
        frule_tac D = C and a = "f b" in Worder.segment_Worder,
        frule_tac D = "Iod C (segment C (f b))" in Worder.Order)
 apply (frule_tac D = "Iod B (segment B b)" and E = "Iod C (segment C (f b))"
         in  Order.ord_equiv, assumption+)
 apply (frule_tac S = A and T = "Iod B (segment B b)" and 
                  U = "Iod C (segment C (f b))" in Worder_trans, assumption+)
 apply (simp add:Order.Iod_carr_segment)
 apply (frule_tac D = C and a = ba in Order.segment_sub,
        frule_tac c = "f b" and A = "segment C ba" and B = "carrier C" in
        subsetD, assumption+)
 apply blast
done

lemma ordinal_numberTr1:" X \<in> carrier ODnods \<Longrightarrow> \<exists>D. Worder D \<and> D \<in> X"
apply (simp add:ODnods_def, simp add:ODnums_def) 
apply (erule exE, erule conjE)
 apply (simp add:ordinal_number_def)
 apply (frule_tac S = S in Worder_refl, blast) 
done

lemma ordinal_numberTr1_1:" X \<in> ODnums \<Longrightarrow> \<exists>D. Worder D \<and> D \<in> X"
apply (simp add:ODnums_def, erule exE, erule conjE, 
       simp add:ordinal_number_def)
 apply (frule_tac S = S in Worder_refl, blast) 
done

lemma ordinal_numberTr1_2:"\<lbrakk>x \<in> ODnums; S \<in> x; T \<in> x\<rbrakk> \<Longrightarrow>
                              ord_equiv S T"
by (simp add:ODnums_def, erule exE, erule conjE,
       simp add:ordinal_number_def, (erule conjE)+,
       frule_tac S = T and T = Sa in Worder_sym, assumption, assumption,
       rule_tac S = S and T = Sa and U = T in Worder_trans, assumption+)

lemma ordinal_numberTr2:"\<lbrakk>Worder D; x = ordinal_number D\<rbrakk> \<Longrightarrow>
            D \<in> x"
by (simp add:ordinal_inc_self)

lemma ordinal_numberTr3:"\<lbrakk>Worder D; Worder F; ord_equiv D F; 
        x = ordinal_number D\<rbrakk> \<Longrightarrow> x = ordinal_number F"
apply (simp add:ordinal_number_def,
        thin_tac "x = {X. Worder X \<and> ord_equiv X D}")
apply (rule equalityI)
 apply (rule subsetI, simp, erule conjE)
 apply (rule_tac S = x and T = D and U = F in Worder_trans, assumption+)
apply (rule subsetI, simp, erule conjE)
 apply (frule Worder_sym [of "D" "F"], assumption+,
        rule_tac S = x and T = F and U = D in Worder_trans, assumption+)
done

lemma ordinal_numberTr4:"\<lbrakk>Worder D; X \<in> carrier ODnods; D \<in> X \<rbrakk> \<Longrightarrow>
            X = ordinal_number D"
apply (simp add:ODnods_def ODnums_def, erule exE, erule conjE)
apply simp
apply (frule_tac D = S in mem_ordinal_number_equiv[of _ "D"], assumption+,
       frule_tac D = D and E = S in ordinal_number_eq, assumption+)
apply simp
done

lemma ordinal_numberTr5:"\<lbrakk>x \<in> ODnums; D \<in> x\<rbrakk> \<Longrightarrow> x = ordinal_number D"
apply (frule mem_ordinal_number_Worder1[of x D], assumption+)
apply (rule ordinal_numberTr4[of D x], assumption,
       simp add:ODnods_def, assumption)
done

lemma ordinal_number_ord:"\<lbrakk> X \<in> carrier ODnods; Y \<in> carrier ODnods\<rbrakk> \<Longrightarrow>
                             ODord X Y \<or> X = Y \<or> ODord Y X"
apply (simp add:ODord_def)
 apply (frule ordinal_numberTr1 [of "X"],
        frule ordinal_numberTr1 [of "Y"], (erule exE)+, rename_tac D E)
 apply (erule conjE)+ 
 apply (frule_tac D = D and E = E in Worder.Word_compare, assumption+)
 apply (erule disjE)+
 apply (erule bexE,
        cut_tac D = D and a = a in Worder.segment_Worder, assumption+,
        frule_tac S = "Iod D (segment D a)" and T = E in Worder_sym, 
        assumption+, blast)

apply (erule disjE) 
 apply (frule_tac D = D and X = X in ordinal_numberTr4, assumption+,
        frule_tac D = E and X = Y in ordinal_numberTr4, assumption+,
        frule_tac D = D and E = E in ordinal_number_eq, assumption+)
 apply simp

apply blast
done 

lemma ODnum_subTr:"\<lbrakk>Worder D; x = ordinal_number D; y \<in>ODnums; y \<sqsubset> x; Y \<in> y\<rbrakk>
                   \<Longrightarrow> \<exists>c\<in>carrier D. ord_equiv Y (Iod D (segment D c))"
apply simp
 apply (thin_tac "x = ordinal_number D")
 apply (simp add:ODnums_def, erule exE, erule conjE, simp,
        thin_tac "y = ordinal_number S")
 apply (frule_tac D = S and X = Y in mem_ordinal_number_Worder, 
                                                      assumption+)
 apply (frule_tac D = Y and X = "ordinal_number S" in ordinal_numberTr4,
        simp add:ODnods_def ODnums_def, blast, simp)
 apply simp
 apply (thin_tac "Y \<in> ordinal_number Y",
        thin_tac "ordinal_number S = ordinal_number Y")
 apply (simp add:ODordTr1[of "Y" "D"])
done

lemma ODnum_segmentTr:"\<lbrakk>Worder D; x = ordinal_number D; y \<in>ODnums; y \<sqsubset> x\<rbrakk> \<Longrightarrow> 
        \<exists>c. c\<in>carrier D \<and> (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c)))"
apply (frule ordinal_numberTr1_1[of "y"], erule exE, erule conjE,
       frule_tac x = x and y = y and Y = Da in ODnum_subTr[of "D" ],
        assumption+, erule bexE)
apply (rule ex_conjI, simp+)

apply (rule ballI)
 apply (frule_tac D = D and a = c in Worder.segment_Worder)
 apply (frule_tac X = Y in mem_ordinal_number_Worder1[of y], assumption)
 apply (subst ordinal_number_eq, assumption+)
 apply (simp add:ordinal_number_eq)
 apply (subst ordinal_numberTr5[THEN sym, of y], assumption+)
 apply (frule_tac D = Da in ordinal_numberTr5[of y], assumption, simp)
done

lemma ODnum_segmentTr1:"\<lbrakk>Worder D; x = ordinal_number D; y \<in> ODnums; y \<sqsubset> x\<rbrakk>
        \<Longrightarrow> \<exists>c. c \<in> carrier D \<and> (y = ordinal_number (Iod D (segment D c)))"
apply (frule ODnum_segmentTr[of D x y], assumption+, erule exE, erule conjE)
apply (frule mem_ODnums_nonempty[of y], erule exE,
       frule_tac x = xa in bspec, assumption,
       thin_tac "\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D c))")
 (** going to apply ordinal_number_eq **)
 apply (frule_tac D = xa in ordinal_numberTr5[of y], assumption, simp,
        frule_tac a = c in Worder.segment_Worder[of D],
        rotate_tac -2, frule sym, thin_tac "y = ordinal_number xa", simp,
        frule_tac X = xa in mem_ordinal_number_Worder1[of y], assumption+)
 apply (simp add:ordinal_number_eq) apply blast
done

lemma ODnods_less:"\<lbrakk>x \<in> carrier ODnods; y \<in> carrier ODnods\<rbrakk> \<Longrightarrow>
                       x \<prec>\<^bsub>ODnods\<^esub> y =  x \<sqsubset> y"
apply (simp add:ODnods_def ole_def oless_def ODrel_def ODord_le_def)
apply (rule iffI)
 apply (erule conjE, erule disjE, simp, assumption, simp)
 apply (simp add:ODord_def, (erule bexE)+)
 apply (rule contrapos_pp, simp+,
        frule_tac x = y and S = ya and T = xa in ordinal_numberTr1_2,
         assumption+)

 apply (simp add:ODnums_def, erule exE, erule conjE, simp,
        frule_tac D = S and X = xa in mem_ordinal_number_Worder, assumption+,
        frule_tac D = S and X = ya in mem_ordinal_number_Worder, assumption+,
        cut_tac D = ya and a = c in Worder.segment_Worder, assumption+)

 apply (frule_tac S = ya and T = xa and U = "Iod ya (segment ya c)" in
        Worder_trans, assumption+,
        frule_tac D = ya and a = c in Worder.nonequiv_segment, assumption+)
 apply simp
done

lemma ODord_less_not_eq:"\<lbrakk>x \<in> carrier ODnods; y \<in> carrier ODnods; x \<sqsubset> y\<rbrakk> \<Longrightarrow>
                          x \<noteq> y"
apply (rule contrapos_pp, simp+)
apply (frule ordinal_numberTr1[of y], erule exE, erule conjE,
       simp add:ODnods_def)
   (* going to see ord_equiv D (Iod D (segment D c)) for some c,
      at first show ordinal_number D = ordinal_number (Iod D (segment D c)) *)
apply (frule_tac D = D in ordinal_numberTr5[of y], assumption+,
       frule_tac D = D and x = y and y = y in ODnum_segmentTr1, assumption+,
       erule exE, erule conjE, simp,
       frule_tac a = c and D = D in Worder.segment_Worder) (* equality got *)
apply (rotate_tac -4, frule sym, 
       thin_tac "ordinal_number (Iod D (segment D c)) = ordinal_number D",
       simp add:ordinal_number_eq[THEN sym]) (* ord_equiv got *)
apply (frule_tac D = D and a = c in Worder.nonequiv_segment, assumption)
       (**** this is the key lemma ****)
apply simp
done

lemma not_ODord:"\<lbrakk>a \<in> ODnums; b \<in> ODnums; a \<sqsubset> b\<rbrakk> \<Longrightarrow> \<not> (b \<sqsubseteq> a)"
apply (rule contrapos_pp, simp+)

apply (simp add:ODord_le_def)
apply (cut_tac x = a and y = b in ODord_less_not_eq,
          simp add:ODnods_def, simp add:ODnods_def, assumption)
apply (erule disjE) apply simp
 (** Show that ord_equiv to segment each other does not happen **) 
 apply (frule ordinal_numberTr1_1[of a],
        frule ordinal_numberTr1_1[of b], (erule exE)+, (erule conjE)+)
 apply (frule_tac D = D in ordinal_numberTr5[of a], assumption,
        frule_tac D = Da in ordinal_numberTr5[of b], assumption, simp)
 apply (frule_tac D = D and E = Da in ODordTr1, assumption+,
        frule_tac D = Da and E = D in ODordTr1, assumption+, simp)
 apply (frule_tac D = D and E = Da in Worder.Word_compareTr3, assumption+)
 apply (erule bexE)+
 apply (frule_tac D = D and a = baa in Worder.segment_Worder,
        frule_tac S = Da and T = "Iod D (segment D baa)" in Worder_sym,
        assumption+) apply blast
 apply assumption
done

lemma Order_ODnods:"Order ODnods"
apply (rule Order.intro)
 apply (simp add:ODnods_def ODrel_def)

 apply (simp add:ODnods_def ODrel_def, simp add:ODord_le_def)
 
 apply (simp add:ODnods_def ODrel_def, simp add:ODord_le_def)
 apply (erule disjE, assumption)
 apply (erule disjE, rule sym, assumption)
 apply (frule_tac a = a and b = b in not_ODord, assumption+)
 apply (simp add:ODord_le_def)

 apply (simp add:ODnods_def ODrel_def)
 apply (rule_tac X = a and Y = b and Z = c in ODord_le_trans, assumption+)
done

lemma Torder_ODnods:"Torder ODnods" 
apply (rule Torder.intro)
apply (cut_tac Order_ODnods, assumption)

 (*** tordered set ***)
 apply (simp add:Torder_axioms_def)
  apply ((rule allI, rule impI)+) 
apply (cut_tac Order_ODnods) 
apply (subst Order.le_imp_less_or_eq[of "ODnods"], assumption+,
       subst Order.le_imp_less_or_eq[of "ODnods"], assumption+)  
apply (simp add:ODnods_less,
       frule_tac X = a and Y = b in ordinal_number_ord, assumption+,
         blast)
done

definition
  ODNmap :: "'a Order \<Rightarrow> ('a Order) set \<Rightarrow> 'a" where
  "ODNmap D y = (SOME z. (z \<in> carrier D \<and> 
                        (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D z)))))" 

lemma ODNmap_mem:"\<lbrakk>Worder D; x = ordinal_number D; y \<in> ODnums; ODord y x\<rbrakk> \<Longrightarrow> 
      ODNmap D y \<in> carrier D \<and> 
             (\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D (ODNmap D y))))" 
apply (frule ODnum_segmentTr [of "D" "x" "y"], assumption+)
apply (simp add:ODNmap_def)
apply (rule someI2_ex, assumption+)
done 

lemma ODNmapTr1:"\<lbrakk>Worder D; x = ordinal_number D; y \<in> ODnums; ODord y x\<rbrakk> \<Longrightarrow> 
                  y = ordinal_number (Iod D (segment D (ODNmap D y)))"
apply (frule ODNmap_mem [of "D" "x" "y"], assumption+, erule conjE,
       frule ODnum_segmentTr1 [of "D" "x" "y"], assumption+)
 apply (erule exE, erule conjE,
        cut_tac D = D and a = c in Worder.segment_Worder, assumption+,
        frule_tac D = "Iod D (segment D c)" and x = y in ordinal_numberTr2,
            assumption+,
        frule_tac x = "Iod D (segment D c)" in bspec, assumption,
         thin_tac "\<forall>Y\<in>y. ord_equiv Y (Iod D (segment D (ODNmap D y)))",
        cut_tac a = "ODNmap D y" in Worder.segment_Worder[of "D"],
         assumption+)
 apply (frule_tac D = "Iod D (segment D c)" and E = "Iod D (segment D (ODNmap D y))" in ordinal_number_eq, assumption+) apply simp
done

lemma ODNmap_self:"\<lbrakk>Worder D; c \<in> carrier D;
       a = ordinal_number (Iod D (segment D c))\<rbrakk> \<Longrightarrow> ODNmap D a = c"
apply (simp add:ODNmap_def)
apply (rule someI2_ex, rule ex_conjI, simp)
 apply (rule ballI, 
        cut_tac Worder.segment_Worder[of "D" "c"], 
        rule_tac X = Y in mem_ordinal_number_equiv[of "Iod D (segment D c)"],
        assumption+)

 apply (erule conjE)
 apply (cut_tac Worder.segment_Worder[of "D" "c"], 
        frule ordinal_inc_self[of "Iod D (segment D c)"],
        frule_tac x = "Iod D (segment D c)" in bspec, assumption)
 apply (frule_tac b = x in Worder.segment_unique[of "D" "c" _], assumption+,
        rule sym, assumption, assumption)
done

lemma ODord_ODNmap_less:"\<lbrakk>Worder D; c \<in> carrier D;
      a = ordinal_number (Iod D (segment D c)); d \<in> carrier D; 
      b = ordinal_number (Iod D (segment D d)); a \<sqsubset> b\<rbrakk> \<Longrightarrow>  
      ODNmap D a \<prec>\<^bsub>D\<^esub> (ODNmap D b)"
apply (frule ODNmap_self [of "D" "c" "a"], assumption+,
       frule ODNmap_self [of "D" "d" "b"], assumption+)
apply simp
apply (subst ord_less_ODord[of D c d a b], assumption+)
 apply simp
done

lemma ODNmap_mem1:" \<lbrakk>Worder D; y \<in> segment ODnods (ordinal_number D)\<rbrakk>
         \<Longrightarrow> ODNmap D y \<in> carrier D"
apply (frule_tac D = D and x = "ordinal_number D" and y = y in ODNmap_mem,
       simp, 
       frule ordinal_number_mem_carrier_ODnods[of "D"],
       simp add:ODnods_def segment_def) 
 apply (simp add:segment_def,
        frule ordinal_number_mem_carrier_ODnods[of "D"], simp,
        erule conjE, simp add:ODnods_def oless_def ole_def ODrel_def)
 apply (simp add:ODord_le_def, blast, simp)
done

lemma ODnods_segment_inc_ODord:"\<lbrakk>Worder D; 
       y \<in> segment ODnods (ordinal_number D)\<rbrakk> \<Longrightarrow> ODord y (ordinal_number D)"
 apply (simp add:segment_def,
        frule ordinal_number_mem_carrier_ODnods[of "D"], simp,
        erule conjE, simp add:ODnods_def oless_def ole_def ODrel_def)
 apply ((erule conjE)+, simp add:ODord_le_def)
done

lemma restict_ODNmap_func:"\<lbrakk>Worder D; x = ordinal_number D\<rbrakk> \<Longrightarrow>
      restrict (ODNmap D) (segment ODnods (ordinal_number D))
               \<in> segment ODnods (ordinal_number D) \<rightarrow> carrier D"
apply (cut_tac Order_ODnods,
       frule Order.Iod_carr_segment[of "ODnods" "ordinal_number D"],
       frule Order.segment_sub[of "ODnods" "ordinal_number D"])
apply (rule Pi_I, simp,
        (frule Order.Iod_carr_segment[of ODnods "ordinal_number D"], 
         simp,
         thin_tac "carrier (Iod ODnods (segment ODnods (ordinal_number D))) =
                            segment ODnods (ordinal_number D) "),
        rule ODNmap_mem1[of D], assumption+)
done

lemma ODNmap_ord_isom:"\<lbrakk>Worder D; x = ordinal_number D\<rbrakk>  \<Longrightarrow> 
             ord_isom (Iod ODnods (segment ODnods x)) D 
      (\<lambda>x\<in>(carrier (Iod ODnods (segment ODnods x))). (ODNmap D x))"
apply (cut_tac Order_ODnods,
       frule Order.Iod_carr_segment[of "ODnods" "ordinal_number D"],
       frule ordinal_number_mem_carrier_ODnods[of D],
       frule Order.segment_sub[of "ODnods" "ordinal_number D"])
       (* above items are preliminary *)
apply (simp add:ord_isom_def)
 apply (rule conjI)
 apply (simp add:ord_inj_def)
 apply (simp add:restict_ODNmap_func[of D x])
 apply (rule conjI)
 apply (subst inj_on_def)  (* show inj_on *)
 apply ((rule ballI)+, rule impI) (* show xa and y is the ordinal_number of
        segments of D *)
  apply (thin_tac "carrier (Iod ODnods (segment ODnods (ordinal_number D))) =
        segment ODnods (ordinal_number D)")
  apply (frule_tac y = xa in ODnods_segment_inc_ODord[of D], assumption+,
         frule_tac y = y in ODnods_segment_inc_ODord[of D], assumption+)
  apply (frule_tac y = y in ODNmapTr1[of D x], assumption+)
  apply (frule_tac c = y in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+, simp add:carr_ODnods,
                   simp)
  apply (frule_tac y = xa in ODNmapTr1[of D x], assumption+)
  apply (frule_tac c = xa in subsetD[of "segment ODnods (ordinal_number D)"
                   "carrier ODnods"], assumption+, simp add:carr_ODnods,
                   simp, simp)
  apply (rule ballI)+
   apply (thin_tac "carrier (Iod ODnods (segment ODnods (ordinal_number D))) =
        segment ODnods (ordinal_number D)")
  apply (frule_tac y = a in ODnods_segment_inc_ODord[of D], assumption+,
         frule_tac y = b in ODnods_segment_inc_ODord[of D], assumption+)
  apply (frule_tac y = a in ODNmapTr1[of D x], assumption+)
  apply (frule_tac c = a in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+, simp add:carr_ODnods,
                   simp)
  apply (frule_tac y = b in ODNmapTr1[of D x], assumption+)
  apply (frule_tac c = b in subsetD[of "segment ODnods (ordinal_number D)"
                   "carrier ODnods"], assumption+, simp add:carr_ODnods,
                   simp)
  apply (frule_tac c = "ODNmap D a" and d = "ODNmap D b" and a = a and b = b in
             ord_less_ODord[of D],
         frule_tac  x = x and y = a in ODNmap_mem[of D], assumption, 
         frule_tac c = a in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+, simp add:carr_ODnods,   
         simp, simp)
  apply (frule_tac  x = x and y = b in ODNmap_mem[of D], assumption, 
         frule_tac c = b in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+, simp add:carr_ODnods,   
         simp, simp) apply simp+
   apply (frule_tac c = a in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+,
          frule_tac c = b in subsetD[of "segment ODnods (ordinal_number D)"
                  "carrier ODnods"], assumption+) 
  apply (simp add:Order.Iod_less[of "ODnods"])
   apply (simp add:ODnods_less)  (** order_preserving proved **)

 apply (rule surj_to_test) (* show surj_to *)
    apply (simp add:restict_ODNmap_func)
    apply (rule ballI,
           cut_tac D = D and a = b in Worder.segment_Worder, assumption+,
           frule_tac D = "Iod D (segment D b)" in 
                                 ordinal_number_mem_carrier_ODnods,
           frule_tac c = b and a = "ordinal_number (Iod D (segment D b))"
            in ODNmap_self, assumption, simp,
           frule_tac d = b in ODord[of D], assumption,
           frule_tac a = "ordinal_number (Iod D (segment D b))" in 
            Order.segment_inc[of "ODnods" _ "ordinal_number D"], assumption+,
           cut_tac x = "ordinal_number (Iod D (segment D b))" in 
                         ODnods_less[of _ "ordinal_number D"], assumption+,
           simp)
    apply (frule_tac c = b and a = "ordinal_number (Iod D (segment D b))" in
            ODNmap_self[of D], assumption)
     apply simp
    apply  blast
done 

lemma ODnum_equiv_segment:"\<lbrakk>Worder D; x = ordinal_number D\<rbrakk>  \<Longrightarrow> 
         ord_equiv (Iod ODnods (segment ODnods x)) D"
apply (simp add: ord_equiv_def)  
apply (frule ODNmap_ord_isom[of "D" "x"], assumption+, blast)
done

lemma ODnods_sub_carrier:"S \<subseteq> ODnums \<Longrightarrow> carrier (Iod ODnods S) = S"
by (simp add:Iod_def)

lemma ODnum_sub_well_ordered:"S \<subseteq> ODnums \<Longrightarrow> Worder (Iod ODnods S)"
apply (cut_tac Torder_ODnods,
       cut_tac Order_ODnods)
 apply (frule Torder.Iod_Torder[of "ODnods" S], 
        simp add:carr_ODnods)
apply intro_locales
 apply (simp add:Torder_def, simp add:Torder_def)

 apply (simp add:Worder_axioms_def,
        rule allI, rule impI, erule conjE)  

(** show existence of the minimum_element of X **)
 apply (frule Order.Iod_carrier[of ODnods S],
        simp add:carr_ODnods, simp)
 apply (frule_tac A = X in nonempty_ex, erule exE)
 apply (frule_tac c = x and A = X and B = S in subsetD, assumption+,
        frule_tac c = x and A = S and B = ODnums in subsetD, assumption+)
 apply (frule_tac X = x in ordinal_numberTr1_1, erule exE, erule conjE)
 apply (frule_tac D = D and x = x in ODnum_equiv_segment) 
 apply (rule ordinal_numberTr4, assumption+, simp add:carr_ODnods, assumption)
 apply (frule_tac D = D and T = "Iod ODnods (segment ODnods x)" in
        Worder.equiv_Worder1,
        rule Order.Iod_Order[of ODnods], assumption,
        rule Order.segment_sub, assumption+)
 apply (frule_tac D = "Iod ODnods (segment ODnods x)" in Worder.ex_minimum)
 apply (case_tac "(segment ODnods x) \<inter> X \<noteq> {}")
 apply (frule_tac a = "segment ODnods x \<inter> X" in forall_spec)
  apply (simp add:Order.Iod_carr_segment)
  apply (thin_tac "\<forall>X. X \<subseteq> carrier (Iod ODnods (segment ODnods x)) \<and> X \<noteq> {}
         \<longrightarrow>  (\<exists>xa. minimum_elem (Iod ODnods (segment ODnods x)) X xa)")
  apply (erule exE)
 
 apply (simp add:carr_ODnods[THEN sym])
 apply (frule_tac A = X and B = S and C = "carrier ODnods" in subset_trans,
        assumption+)
apply (frule_tac d = x and m = xa and X = X in 
        Torder.segment_minimum_minimum[of ODnods], assumption+,
        simp add:Int_commute, 
        simp add:Order.minimum_elem_sub[of ODnods S], blast)
 apply (simp,
       thin_tac "\<forall>X. X \<subseteq> carrier (Iod ODnods (segment ODnods x)) \<and> X \<noteq> {} \<longrightarrow>
            (\<exists>xa. minimum_elem (Iod ODnods (segment ODnods x)) X xa)")
 apply (frule_tac A = "segment ODnods x" and B = X in no_meet2)
 apply (simp add:carr_ODnods[THEN sym])
 apply (frule_tac A = X and B = S and C = "carrier ODnods" in subset_trans,
        assumption+)
 apply (frule_tac A = X and B = S and C = "carrier ODnods" in subset_trans,
        assumption+)
 apply (simp add:Order.segment_inc[THEN sym, of ODnods])
 apply (rule contrapos_pp, simp+)
 apply (frule_tac x = x in spec,
        thin_tac "\<forall>x. \<not> minimum_elem (Iod ODnods S) X x")
 apply (simp add:minimum_elem_def, erule bexE)
 apply (frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>a\<in>X. a \<notin> segment ODnods x",
        frule_tac c = xa and A = X and B = "carrier ODnods" in subsetD,
        assumption+)
 apply (simp add:Order.segment_inc[of ODnods, THEN sym],
        frule_tac c = xa and A = X and B = S in subsetD, assumption+)
 apply (simp add:Order.Iod_le[of ODnods S])
 apply (simp add:Torder.not_le_less)
done

section "Pre elements"  

definition
  ExPre :: "_ \<Rightarrow> 'a \<Rightarrow> bool" where
  "ExPre D a \<longleftrightarrow> (\<exists>x. x \<in> carrier D \<and> x \<prec>\<^bsub>D\<^esub> a 
                      \<and> \<not> (\<exists>y\<in>carrier D. x \<prec>\<^bsub>D\<^esub> y \<and> y \<prec>\<^bsub>D\<^esub> a))" 
     (* exists pre element *)

definition
  Pre :: "[_ ,  'a] \<Rightarrow> 'a" where
  "Pre D a = (SOME x. x \<in> carrier D \<and> 
                           x \<prec>\<^bsub>D\<^esub> a \<and>
                         \<not> (\<exists>y\<in>carrier D. x \<prec>\<^bsub>D\<^esub> y \<and> y \<prec>\<^bsub>D\<^esub> a))"
     (* Pre element of a *)

lemma (in Order) Pre_mem:"\<lbrakk>a \<in> carrier D; ExPre D a\<rbrakk> \<Longrightarrow>
                Pre D a \<in> carrier D"
apply (simp add:ExPre_def)
 apply (subst Pre_def, rule someI2_ex, blast, simp)
done

lemma (in Order) Not_ExPre:"a \<in> carrier D \<Longrightarrow> \<not> ExPre (Iod D {a}) a"
apply (simp add:ExPre_def,
       rule allI, rule impI, rule impI,
       frule singleton_sub[of "a" "carrier D"])
apply (simp add:Iod_less Iod_carrier)
done

lemma (in Worder) UniquePre:"\<lbrakk>a \<in> carrier D; ExPre D a;
 a1 \<in> carrier D \<and> a1 \<prec> a \<and> \<not> (\<exists>y\<in>carrier D. (a1 \<prec> y \<and> y \<prec> a)) \<rbrakk> \<Longrightarrow>
 Pre D a = a1"
apply (simp add:ExPre_def)
apply (subst Pre_def)        (* definition *)
apply (rule someI2_ex, blast)
apply (erule conjE)+
 apply (thin_tac "\<exists>x. x \<in> carrier D \<and> x \<prec> a \<and>
                           (\<forall>y\<in>carrier D. x \<prec> y \<longrightarrow> \<not> y \<prec> a)",
        rename_tac z)
 apply (rule contrapos_pp, simp+) 
 apply (frule_tac a = z and b = a1 in less_linear, assumption+,
        simp)
 apply (erule disjE)
 apply (rotate_tac -4,
        frule_tac x = a1 in bspec, assumption+,
        thin_tac "\<forall>y\<in>carrier D. z \<prec> y \<longrightarrow> \<not> y \<prec> a",
        thin_tac "\<forall>y\<in>carrier D. a1 \<prec> y \<longrightarrow> \<not> y \<prec> a", simp)

 apply (frule_tac x = z in bspec, assumption+, simp)
done

lemma (in Order) Pre_element:"\<lbrakk>a \<in> carrier D; ExPre D a\<rbrakk> \<Longrightarrow> 
      Pre D a \<in> carrier D \<and> (Pre D a) \<prec> a \<and>
            \<not> (\<exists>y\<in>carrier D. ((Pre D a) \<prec> y \<and> y \<prec> a))"
apply (simp add:ExPre_def)
apply (subst Pre_def)+
apply (rule someI2_ex)
apply simp+
done

lemma (in Order) Pre_in_segment:"\<lbrakk>a \<in> carrier D; ExPre D a\<rbrakk> \<Longrightarrow> 
                  Pre D a \<in> segment D a"
by (frule Pre_element[of "a"], assumption+, (erule conjE)+,
    simp add:segment_inc) 

lemma (in Worder) segment_forall:"\<lbrakk>a \<in> segment D b; b \<in> carrier D; 
      x \<in> segment D b; x \<prec> a; \<forall>y\<in>segment D b. x \<prec> y \<longrightarrow> \<not> y \<prec> a\<rbrakk> \<Longrightarrow> 
      \<forall>y\<in>carrier D. x \<prec> y \<longrightarrow> \<not> y \<prec> a"
apply (cut_tac segment_sub[of b])
apply (rule ballI, rule impI) 
 apply (case_tac "y \<in> segment D b",
         frule_tac x = y in bspec, assumption+, simp)
(***  
        ------------------a---------------b---------------y----------
***)
 apply (thin_tac "\<forall>y\<in>segment D b. x \<prec> y \<longrightarrow> \<not> y \<prec> a",
         frule subsetD[of "segment D b" "carrier D" "a"], assumption+,
         frule_tac c = x in subsetD[of "segment D b" "carrier D"], assumption+,
         thin_tac "segment D b \<subseteq> carrier D",
         thin_tac "x \<in> segment D b")
 apply (simp add:segment_inc[THEN sym, of _ "b"]) apply (
         simp add:not_less_le)
 apply (frule_tac c = y in less_le_trans[of a b], assumption+)
 apply (simp add:less_imp_le)
done

lemma (in Worder) segment_Expre:"a \<in> segment D b \<Longrightarrow>
                   ExPre (Iod D (segment D b)) a = ExPre D a"
apply (case_tac "b \<notin> carrier D")
 apply (simp add:segment_def Iod_self[THEN sym])

apply simp
apply (cut_tac segment_sub[of "b"],
       frule subsetD[of "segment D b" "carrier D" a], assumption+)
apply (rule iffI)
 apply (simp add:ExPre_def, erule exE, (erule conjE)+)
 apply (simp add:Iod_carrier Iod_less) 
 apply (frule_tac x = x in segment_forall[of "a" "b"], assumption+)
 apply blast

 apply (simp add:ExPre_def, erule exE, (erule conjE)+)
  apply (frule_tac a = a in segment_inc[of _ b], assumption, simp)
  apply (rule contrapos_pp, simp+)  
  apply (frule_tac x = x in spec,
         thin_tac "\<forall>x. x \<prec>\<^bsub>Iod D (segment D b)\<^esub> a \<longrightarrow>
             x \<in> carrier (Iod D (segment D b)) \<longrightarrow>
             (\<exists>y\<in>carrier (Iod D (segment D b)).
                 x \<prec>\<^bsub>Iod D (segment D b)\<^esub> y \<and> y \<prec>\<^bsub>Iod D (segment D b)\<^esub> a)",
         frule_tac a = x in less_trans[of _ a b], assumption+,
         frule_tac a = x in segment_inc[of _ b], assumption+, simp)
  apply (simp add:Iod_carrier Iod_less)
  apply (erule bexE, erule conjE,
       frule_tac c = y in subsetD[of "segment D b" "carrier D"], assumption+) 
  apply (frule_tac x = y in bspec, assumption,
         thin_tac "\<forall>y\<in>carrier D. x \<prec> y \<longrightarrow> \<not> y \<prec> a", simp)
done

lemma  (in Worder) Pre_segment:"\<lbrakk>a \<in> segment D b; 
        ExPre (Iod D (segment D b)) a\<rbrakk> \<Longrightarrow> 
        ExPre D a \<and> Pre D a = Pre (Iod D (segment D b)) a"
apply (frule segment_Expre[of "a" "b"], simp)
apply (case_tac "b \<notin> carrier D")
      apply (simp add:segment_def, simp add:Iod_self[THEN sym])
      apply simp

apply (cut_tac segment_sub[of "b"],
       frule subsetD[of "segment D b" "carrier D" "a"], assumption+)
     apply (frule_tac a = a and ?a1.0 = "Pre (Iod D (segment D b)) a" in 
            UniquePre, assumption+)
     apply simp
 apply (cut_tac segment_Worder[of "b"]) 
 apply (frule_tac D = "Iod D (segment D b)" in Worder.Order) 
 apply (frule Order.Pre_element[of "Iod D (segment D b)" a],
        simp add:Iod_carrier, assumption, erule conjE, 
        simp add:Iod_carrier, simp add:subsetD, simp add:Iod_less)
 apply (erule conjE, rule ballI)
 apply (case_tac "y \<in> segment D b",
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>segment D b. Pre (Iod D (segment D b)) a \<prec> y 
                  \<longrightarrow> \<not> y \<prec> a",
        simp)
  apply (rule impI)
  apply (frule subsetD[of "segment D b" "carrier D" a], assumption+)
  apply (frule_tac a = y in segment_inc[of _ b], assumption+, simp,
         frule segment_inc[of a b], assumption+, simp)
  apply (simp add:not_less_le)
  apply (frule_tac c = y in less_le_trans[of a b], assumption+,
         simp add:less_imp_le)
  apply assumption
done

lemma (in Worder) Pre2segment:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; b \<prec> a; 
                 ExPre D b\<rbrakk> \<Longrightarrow> ExPre (Iod D (segment D a)) b"
apply (frule segment_inc [of b a], assumption+, simp)
apply (simp add:segment_Expre[of b a])
done

lemma (in Worder) ord_isom_Pre1:"\<lbrakk>Worder E; a \<in> carrier D; ExPre D a; 
                  ord_isom D E f\<rbrakk> \<Longrightarrow> ExPre E (f a)"
apply (simp add:ExPre_def) 
apply (erule exE,
       frule Worder.Order[of "E"],
       erule conjE,
       frule_tac a = x in ord_isom_mem[of "E" "f"], assumption+,
       frule_tac a = a in ord_isom_mem[of "E" "f"], assumption+,
       erule conjE)
 apply (frule_tac a = x in ord_isom_less[of "E" "f" _ "a"], assumption+, simp)
 apply (frule ord_isom_less_forall[of "E" "f"], assumption+)
 apply (frule_tac x = x and a = a in ord_isom_convert[of "E" "f"],
                             assumption+, simp) apply blast
done      (** Here, ord_isom_convert transforms the inequality **)

lemma (in Worder) ord_isom_Pre11:"\<lbrakk>Worder E; a \<in> carrier D; ord_isom D E f\<rbrakk> 
       \<Longrightarrow> ExPre D a = ExPre E (f a)"
apply (rule iffI)
 apply (simp add:ord_isom_Pre1)
 apply (frule Worder.Order[of "E"],
        frule ord_isom_sym[of "E" "f"], assumption+)
 apply (cut_tac Worder)
  apply (frule Worder_ord_isom_mem[of "D" "E" "f" "a"], assumption+,
         frule Worder.ord_isom_Pre1[of "E" "D" "f a" 
              "invfun (carrier D) (carrier E) f"], assumption+)
 apply (frule ord_isom_func[of "E" "f"], assumption+)
 apply (simp add:ord_isom_def[of "D" "E" "f"] ord_inj_def, (erule conjE)+,
        thin_tac "\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. a \<prec> b = f a \<prec>\<^bsub>E\<^esub> f b")
 apply (simp add:invfun_l)
done

lemma (in Worder) ord_isom_Pre2:"\<lbrakk>Worder E; a \<in> carrier D; ExPre D a; 
       ord_isom D E f\<rbrakk> \<Longrightarrow> f (Pre D a) = Pre E (f a)" 
apply (frule_tac E = E and a = a and f = f in ord_isom_Pre1, assumption+,
       frule_tac a = a in Pre_element, assumption+, (erule conjE)+)
 apply (frule Worder.Order[of "E"], 
        frule  ord_isom_mem[of "E" "f" "a"], assumption+,
        frule  ord_isom_mem[of "E" "f" "Pre D a"], assumption+,
        simp add:ord_isom_less[of "E" "f" "Pre D a" "a"]) 
 apply (simp add:ord_isom_convert[of E f "Pre D a" a])
 apply (rule Worder.UniquePre[THEN sym, of "E" "f a" "f (Pre D a)"],
        assumption+, simp) 
done

section "Transfinite induction"

lemma (in Worder) transfinite_induction:"\<lbrakk>minimum_elem D (carrier D) s0; P s0; \<forall>t\<in>carrier D. ((\<forall>u\<in> segment D t. P u) \<longrightarrow> P t)\<rbrakk> \<Longrightarrow> \<forall>x\<in>carrier D. P x" 
apply (rule contrapos_pp, simp+)
 apply (frule bex_nonempty_set[of "carrier D"],
        frule nonempty_set_sub[of "carrier D"])
 apply (cut_tac ex_minimum)
 apply (frule_tac a = "{x \<in> carrier D. \<not> P x}" in forall_spec,
        simp,
        thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)")
  apply (thin_tac "\<exists>x\<in>carrier D. \<not> P x")
  apply (erule exE)
  apply (frule_tac d = x in less_minimum)
  apply (frule_tac X = "{x \<in> carrier D. \<not> P x}" and a = x in minimum_elem_mem,
         assumption+)
  apply (frule_tac c = x and A = "{x \<in> carrier D. \<not> P x}" and B = "carrier D"
          in subsetD, assumption+) 
  apply (frule_tac x = x in bspec, assumption+,
         thin_tac "\<forall>t\<in>carrier D. (\<forall>u\<in>segment D t. P u) \<longrightarrow> P t")
  apply (simp add:minimum_elem_def, (erule conjE)+) 
  apply (erule bexE, simp add:segment_def)
done

section \<open>\<open>Ordered_set2\<close>. Lemmas to prove Zorn's lemma.\<close>
 
definition
  adjunct_ord ::"[_ , 'a] \<Rightarrow> _" where
  "adjunct_ord D a = D \<lparr>carrier := carrier D \<union> {a},
                       rel := {(x,y). (x, y) \<in> rel D \<or> 
                                     (x \<in> (carrier D \<union> {a}) \<and> y = a)}\<rparr> " 

lemma (in Order) carrier_adjunct_ord:
        "carrier (adjunct_ord D a) = carrier D \<union> {a}"
by (simp add:adjunct_ord_def)

lemma (in Order) Order_adjunct_ord:"a \<notin> carrier D \<Longrightarrow> 
                                    Order (adjunct_ord D a)"
apply (cut_tac closed)
apply (rule Order.intro)
 apply (rule subsetI)
 apply (unfold split_paired_all)
 apply simp
 apply (simp add:adjunct_ord_def insert_absorb)
 apply blast

 apply (simp add:carrier_adjunct_ord)
 apply (erule disjE)
 apply (simp add:adjunct_ord_def)
 apply (simp add:adjunct_ord_def)
 apply (simp add:refl)

 apply (simp add:adjunct_ord_def)
  apply (erule disjE)+
  apply simp+
  apply (erule disjE) 
  apply (frule_tac c = "(a, b)" in subsetD[of "rel D" "carrier D \<times> carrier D"],
         assumption+)
  apply blast
  apply simp

  apply (erule disjE)+
  apply (cut_tac closed, simp+)
  apply (frule_tac c = "(a, aa)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+, simp)
  apply (frule_tac c = "(aa, b)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+, simp)

  apply (erule disjE)
  apply (frule_tac c = "(b, aa)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+)
  apply simp+

  apply (erule disjE)+
  apply (rule antisym, assumption+)

  apply (frule_tac c = "(aa, b)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+)
    apply simp 
 
  apply (erule disjE)
  apply (frule_tac c = "(b, aa)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+,
         simp, simp)  

apply (simp add:adjunct_ord_def)
 apply (erule disjE)+
 apply blast
 apply blast
 apply blast

apply (erule disjE)
 apply simp
 apply (erule disjE)
 apply (frule_tac c = "(b, c)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+)
       apply simp apply blast
 apply (erule disjE, blast)
 apply (erule disjE) 
 apply simp
 apply (erule disjE)
 apply (frule_tac c = "(a, b)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+, simp)
 apply (frule_tac c = "(a, b)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+, simp)
 apply (erule disjE, simp) apply blast
 apply (erule disjE) apply simp
 apply (erule disjE) apply blast
 apply (erule disjE) 
 apply (frule_tac c = "(a, c)" in subsetD[of "rel D" 
                              "carrier D \<times> carrier D"], assumption+, simp)
 apply blast
 apply (erule disjE)+
 apply blast apply blast apply blast
 apply (erule disjE)
 apply (erule disjE)
 apply (frule_tac a = aa and b = b and c = c in trans, assumption+)
         apply simp
   apply blast
 apply (erule disjE) apply simp apply blast
done

lemma (in Order) adjunct_ord_large_a:"\<lbrakk>Order D; a \<notin> carrier D\<rbrakk> \<Longrightarrow> 
                             \<forall>x\<in>carrier D. x \<prec>\<^bsub>adjunct_ord D a\<^esub> a"
apply (rule ballI)          
apply (subst oless_def)
apply (rule conjI)
apply (simp add:ole_def adjunct_ord_def)
apply (rule contrapos_pp, simp+)
done  

lemma carr_Ssegment_adjunct_ord:"\<lbrakk>Order D; a \<notin> carrier D\<rbrakk> \<Longrightarrow> 
                 carrier D = (Ssegment (adjunct_ord D a) a)" 
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:Ssegment_def Order.carrier_adjunct_ord)
 apply (simp add:Order.adjunct_ord_large_a)
 
apply (rule subsetI)
 apply (simp add:Ssegment_def Order.carrier_adjunct_ord)
 apply (erule conjE)
 apply (erule disjE, simp add:oless_def)
 apply assumption
done

lemma (in Order) adjunct_ord_selfD:"a \<notin> carrier D \<Longrightarrow>
          D = Iod (adjunct_ord D a) (carrier D)"
apply (simp add:Iod_def)
apply (simp add:adjunct_ord_def)
apply (subgoal_tac "rel D = {(aa, b).
              ((aa, b) \<in> rel D \<or> (aa = a \<or> aa \<in> carrier D) \<and> b = a) \<and>
              aa \<in> carrier D \<and> b \<in> carrier D}")
apply simp
apply (rule equalityI)
 apply (rule subsetI)
 apply (cut_tac closed,
        frule_tac c = x in subsetD[of "rel D" "carrier D \<times> carrier D"],
        assumption+)
apply auto
done

lemma Ssegment_adjunct_ord:"\<lbrakk>Order D; a \<notin> carrier D\<rbrakk> \<Longrightarrow> 
          D = SIod (adjunct_ord D a) (Ssegment (adjunct_ord D a) a)" 
apply (simp add: carr_Ssegment_adjunct_ord[THEN sym, of "D" "a"])
apply (frule Order.Order_adjunct_ord[of "D" "a"], assumption+)
apply (cut_tac Order.carrier_adjunct_ord[THEN sym, of "D" "a"])
apply (cut_tac Un_upper1[of "carrier D" "{a}"], simp)
apply (subst SIod_self_le[THEN sym, of "adjunct_ord D a" "D"],
        assumption+)
apply (rule ballI)+
apply (frule_tac c = aa in subsetD[of "carrier D" "carrier (adjunct_ord D a)"],
        assumption,
       frule_tac c = b in subsetD[of "carrier D" "carrier (adjunct_ord D a)"],
        assumption)
apply (simp add:Order.le_rel[of "adjunct_ord D a"])
apply (subst adjunct_ord_def, simp)
 apply (case_tac "b = a", simp) apply simp
 apply (simp add:Order.le_rel[of "D"])
apply simp+
done

lemma (in Order) Torder_adjunction:"\<lbrakk>X \<subseteq> carrier D; a \<in> carrier D; 
      \<forall>x\<in>X. x \<preceq> a; Torder (Iod D X)\<rbrakk> \<Longrightarrow> Torder (Iod D (X \<union> {a}))"
apply (frule insert_sub[of "X" "carrier D" "a"], assumption)
apply (subst Torder_def)
apply (frule singleton_sub[of "a" "carrier D"],
       frule Un_least[of "X" "carrier D" "{a}"], assumption) 

apply (rule conjI)
 apply (simp add:Iod_Order[of "insert a X"])
 
 apply (subst Torder_axioms_def)
 apply ((rule allI)+, (rule impI)+)
 apply (simp only:Iod_carrier, simp add:Iod_le)
 apply (erule disjE, simp) apply (erule disjE, simp)
 apply (simp add:le_refl) apply blast
 apply (erule disjE, simp)
 apply (simp add:Torder_def, simp add:Torder_axioms_def)
 apply (simp add:Iod_carrier, erule conjE)
 apply (frule_tac a = aa in forall_spec, assumption,
        thin_tac "\<forall>a. a \<in> X \<longrightarrow> (\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> a)",
        frule_tac a = b in forall_spec, assumption,
        thin_tac "\<forall>b. b \<in> X \<longrightarrow> aa \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> aa",
        simp add:Iod_le)
done

lemma Torder_Sadjunction:"\<lbrakk>Order D; X \<subseteq> carrier D; a \<in> carrier D; 
      \<forall>x\<in>X. x \<preceq>\<^bsub>D\<^esub> a; Torder (SIod D X)\<rbrakk> \<Longrightarrow> Torder (SIod D (X \<union> {a}))"
apply (frule insert_sub[of "X" "carrier D" "a"], assumption)
apply (subst Torder_def)
apply (frule singleton_sub[of "a" "carrier D"],
       frule Un_least[of "X" "carrier D" "{a}"], assumption) 

apply (rule conjI)
 apply (simp add:SIod_Order[of _ "insert a X"])
 
 apply (subst Torder_axioms_def)
 apply ((rule allI)+, (rule impI)+)
 apply (simp only:SIod_carrier, simp add:SIod_le)
 apply (erule disjE, simp) apply (erule disjE, simp)
 apply (simp add:Order.le_refl) apply blast
 apply (erule disjE, simp)
 apply (simp add:Torder_def, simp add:Torder_axioms_def)
 apply (simp add:SIod_carrier, erule conjE)
 apply (frule_tac a = aa in forall_spec, assumption,
       thin_tac "\<forall>a. a \<in> X \<longrightarrow> (\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>SIod D X\<^esub> b \<or> b \<preceq>\<^bsub>SIod D X\<^esub> a)",
       frule_tac a = b in forall_spec, assumption,
       thin_tac "\<forall>b. b \<in> X \<longrightarrow> aa \<preceq>\<^bsub>SIod D X\<^esub> b \<or> b \<preceq>\<^bsub>SIod D X\<^esub> aa",
        simp add:SIod_le)
done

lemma (in Torder) Torder_adjunct_ord:"a \<notin> carrier D \<Longrightarrow> 
                                       Torder (adjunct_ord D a)"
apply (frule Order_adjunct_ord[of "a"],
       cut_tac carrier_adjunct_ord[THEN sym, of a],
       cut_tac Un_upper1[of "carrier D" "{a}"], simp,
       frule Order.Torder_adjunction[of "adjunct_ord D a" "carrier D" a],
       assumption+)
 apply (simp add:carrier_adjunct_ord)
 apply (cut_tac adjunct_ord_large_a[of a],
        rule ballI, 
        frule_tac x = x in bspec, assumption,
              thin_tac "\<forall>x\<in>carrier D. x \<prec>\<^bsub>adjunct_ord D a\<^esub> a",
        cut_tac insertI1[of a "carrier D"], simp,
        frule_tac c = x in subsetD[of "carrier D" "carrier (adjunct_ord D a)"],
         assumption+,
        simp add:Order.less_imp_le, rule Order,
        assumption+)
 apply (simp add:adjunct_ord_selfD[THEN sym])
prefer 2
 apply (simp add:Order.Iod_self[THEN sym, of "adjunct_ord D a"])
apply (unfold_locales) 
done

lemma (in Order) well_ord_adjunction:"\<lbrakk>X \<subseteq> carrier D; a \<in> carrier D; 
      \<forall>x\<in>X. x \<preceq> a; Worder (Iod D X)\<rbrakk> \<Longrightarrow> Worder (Iod D (X \<union> {a}))"
apply (frule insert_sub[of "X" "carrier D" "a"], assumption)
apply (subst Worder_def)
 apply (simp add:Iod_Order)
 apply (frule_tac Torder_adjunction[of X a], assumption+)
 apply (simp add:Worder.Torder)
 apply (simp add:Torder_def)

apply (subst Worder_axioms_def)
 apply (rule allI, rule impI, erule conjE)
 apply (simp add:Iod_carrier)
 apply (cut_tac insert_inc1[of "X" "a"])

 apply (case_tac "Xa \<subseteq> X")
 apply (simp only:Worder_def, (erule conjE)+) apply (
        simp only:Worder_axioms_def)
 apply (frule_tac a = Xa in forall_spec,
        thin_tac "\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (Iod D X) Xa x)",
        simp add:Iod_carrier)
 apply (thin_tac "\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (Iod D X) Xa x)",
        erule exE)
 apply (frule_tac X = Xa and a = x in Order.minimum_elem_sub[of 
         "Iod D (insert a X)" "X"])
  apply (cut_tac insert_inc1[of "X" "a"], simp add:Iod_carrier, assumption+)
 apply (cut_tac insert_inc1[of "X" "a"],
        simp add:Iod_sub_sub) apply blast
 apply (erule conjE,
       frule_tac A = Xa in insert_diff[of _ "a" "X"])
 apply (case_tac "Xa - {a} = {}")
 apply (frule_tac A = Xa in nonempty_ex, erule exE, simp, 
        frule_tac c = x and A = Xa and B = "{a}" in subsetD, assumption+,
        simp, 
        frule_tac A = Xa in singleton_sub[of "a"],
        frule_tac A = Xa and B = "{a}" in equalityI, assumption+, simp)
 apply (simp add:minimum_elem_def)
 apply (cut_tac insert_inc2[of "a" "X"],
        simp add:Iod_le le_refl)

 apply (simp only:Worder_def, (erule conjE)+,
        simp only:Worder_axioms_def)
 apply (frule_tac a = "Xa - {a}" in forall_spec, 
        thin_tac "\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (Iod D X) Xa x)", simp add:Iod_carrier)
 apply (thin_tac "\<forall>Xa. Xa \<subseteq> carrier (Iod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (Iod D X) Xa x)", erule exE)
 apply (frule_tac Y = Xa and x = x in augmented_set_minimum[of "X" "a"],
        assumption+, blast)
done

lemma well_ord_Sadjunction:"\<lbrakk>Order D; X \<subseteq> carrier D; a \<in> carrier D; 
      \<forall>x\<in>X. x \<preceq>\<^bsub>D\<^esub> a; Worder (SIod D X)\<rbrakk> \<Longrightarrow> Worder (SIod D (X \<union> {a}))"
apply (frule insert_sub[of "X" "carrier D" "a"], assumption)
apply (subst Worder_def)
 apply (simp add:SIod_Order)
 apply (frule Torder_Sadjunction[of D X a], assumption+)
 apply (simp add:Worder.Torder)
 apply (simp add:Torder_def)

 apply (subst Worder_axioms_def)
 apply (rule allI, rule impI, erule conjE)
 apply (simp add:SIod_carrier)
 apply (cut_tac insert_inc1[of "X" "a"])

 apply (case_tac "Xa \<subseteq> X")
 apply (simp only:Worder_def, (erule conjE)+) apply (
        simp only:Worder_axioms_def)
 apply (frule_tac a = Xa in forall_spec,
        thin_tac "\<forall>Xa. Xa \<subseteq> carrier (SIod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (SIod D X) Xa x)",
        simp add:SIod_carrier)
 apply (thin_tac "\<forall>Xa. Xa \<subseteq> carrier (SIod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (SIod D X) Xa x)",
        erule exE)
 apply (frule_tac X = Xa and a = x in minimum_elem_Ssub[of 
         "SIod D (insert a X)" "X"])
  apply (cut_tac insert_inc1[of "X" "a"], simp add:SIod_carrier, assumption+)
 apply (cut_tac insert_inc1[of "X" "a"],
        simp add:SIod_sub_sub) apply blast

 apply (erule conjE, frule_tac A = Xa in insert_diff[of _ "a" "X"])
 apply (case_tac "Xa - {a} = {}")
 apply (frule_tac A = Xa in nonempty_ex, erule exE, simp, 
        frule_tac c = x and A = Xa and B = "{a}" in subsetD, assumption+,
        simp, 
        frule_tac A = Xa in singleton_sub[of "a"],
        frule_tac A = Xa and B = "{a}" in equalityI, assumption+, simp)
 apply (simp add:minimum_elem_def)
 apply (cut_tac insert_inc2[of "a" "X"],
        simp add:SIod_le Order.le_refl)

 apply (simp only:Worder_def, (erule conjE)+,
        simp only:Worder_axioms_def)
 apply (frule_tac a = "Xa - {a}" in forall_spec, 
        thin_tac "\<forall>Xa. Xa \<subseteq> carrier (SIod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (SIod D X) Xa x)", simp add:SIod_carrier)
 apply (thin_tac "\<forall>Xa. Xa \<subseteq> carrier (SIod D X) \<and> Xa \<noteq> {} \<longrightarrow>
               (\<exists>x. minimum_elem (SIod D X) Xa x)", erule exE)
 apply (frule_tac Y = Xa and x = x in augmented_Sset_minimum[of "D" "X" "a"],
        assumption+, blast) 
done

lemma (in Worder) Worder_adjunct_ord:"a \<notin> carrier D \<Longrightarrow> 
                                       Worder (adjunct_ord D a)"
apply (frule Torder_adjunct_ord[of a])
 apply (intro_locales)
 apply (simp add:Torder_def)
 apply (simp add:Torder_def)

 apply (cut_tac carrier_adjunct_ord[THEN sym, of a],
       cut_tac Un_upper1[of "carrier D" "{a}"], simp)
 apply (simp add:Torder_def, erule conjE) 
 apply (cut_tac insertI1[of a "carrier D" ])
 apply (frule Order.well_ord_adjunction[of "adjunct_ord D a" "carrier D" a],
        assumption+)
 apply (frule sym, thin_tac "insert a (carrier D) = carrier (adjunct_ord D a)",
        simp)
 apply (cut_tac adjunct_ord_large_a[of a],
        rule ballI, 
        frule_tac x = x in bspec, assumption,
              thin_tac "\<forall>x\<in>carrier D. x \<prec>\<^bsub>adjunct_ord D a\<^esub> a",
        cut_tac insertI1[of a "carrier D"], simp,
        frule_tac c = x in subsetD[of "carrier D" "carrier (adjunct_ord D a)"],
         assumption+,
        simp add:Order.less_imp_le, rule Order,
        assumption+)
  apply (simp add:adjunct_ord_selfD[THEN sym])
  prefer 2
  apply (simp add:Order.Iod_self[THEN sym, of "adjunct_ord D a"] Worder_def)
  apply unfold_locales
done
 
section "Zorn's lemma"

definition
  Chain :: "_ \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Chain D C \<longleftrightarrow> C \<subseteq> carrier D \<and> Torder (Iod D C)" 

definition
  upper_bound :: "[_, 'a set, 'a] \<Rightarrow> bool"
    ("(3ub\<index>/ _/ _)" [100,101]100) where
  "ub\<^bsub>D\<^esub> S b \<longleftrightarrow> b \<in> carrier D \<and> (\<forall>s\<in>S. s \<preceq>\<^bsub>D\<^esub> b)" 

definition
  "inductive_set" :: "_ \<Rightarrow> bool" where
  "inductive_set D \<longleftrightarrow> (\<forall>C. (Chain D C \<longrightarrow> (\<exists>b. ub\<^bsub>D\<^esub> C b)))"

definition
  maximal_element :: "[_, 'a] \<Rightarrow> bool"  ("(maximal\<index>/ _)" [101]100) where
  "maximal\<^bsub>D\<^esub> m \<longleftrightarrow> m \<in> carrier D \<and> (\<forall>b\<in>carrier D. m \<preceq>\<^bsub>D\<^esub> b \<longrightarrow> m = b)"

definition
  upper_bounds::"[_, 'a set] \<Rightarrow> 'a set" where
  "upper_bounds D H = {x. ub\<^bsub>D\<^esub> H x}"

definition
  Sup :: "[_, 'a set] \<Rightarrow> 'a" where
  "Sup D X = (THE x. minimum_elem D (upper_bounds D X) x)"

definition
  S_inductive_set :: "_ \<Rightarrow> bool" where
  "S_inductive_set D \<longleftrightarrow> (\<forall>C. Chain D C \<longrightarrow> 
    (\<exists>x\<in>carrier D. minimum_elem D (upper_bounds D C) x))" 

lemma (in Order) mem_upper_bounds:"\<lbrakk>X \<subseteq> carrier D; b \<in> carrier D; 
                 \<forall>x\<in>X. x \<preceq> b\<rbrakk> \<Longrightarrow> ub X b"
apply (simp add:upper_bounds_def upper_bound_def)
done  

lemma (in Order) Torder_Chain:"\<lbrakk>X \<subseteq> carrier D; Torder (Iod D X)\<rbrakk>
       \<Longrightarrow> Chain D X"
apply (simp add:Chain_def Torder_def) 
done

lemma (in Order) Chain_Torder:"Chain D X \<Longrightarrow> 
                                   Torder (Iod D X)"
apply (simp add:Chain_def) 
done

lemma (in Order) Chain_sub:"Chain D X \<Longrightarrow> X \<subseteq> carrier D"
apply (simp add:Chain_def)
done

lemma (in Order) Chain_sub_Chain:"\<lbrakk>Chain D X; Y \<subseteq> X \<rbrakk> \<Longrightarrow> Chain D Y"
apply (frule Chain_sub[of "X"],
       frule Chain_Torder[of "X"],
       frule Torder.Iod_Torder[of "Iod D X" "Y"], simp add:Iod_carrier)
apply (simp add:Iod_sub_sub[of "Y" "X"],
       frule subset_trans[of "Y" "X" "carrier D"], assumption+)
apply (simp add:Torder_Chain[of "Y"])
done

lemma (in Order) upper_bounds_sub:"X \<subseteq> carrier D \<Longrightarrow> 
                           upper_bounds D X \<subseteq> carrier D"
by (rule subsetI, simp add:upper_bounds_def upper_bound_def)


lemma (in Order) Sup:"\<lbrakk>X \<subseteq> carrier D; minimum_elem D (upper_bounds D X) a\<rbrakk> \<Longrightarrow>                        Sup D X = a"
apply (subst Sup_def)
apply (rule the_equality, assumption,
       rule_tac ?a1.0 = x in minimum_elem_unique[of "upper_bounds D X" _ "a"])
 apply (rule subsetI, thin_tac "minimum_elem D (upper_bounds D X) a",
        thin_tac "minimum_elem D (upper_bounds D X) x",
        simp add:upper_bounds_def upper_bound_def)
 apply assumption+
done 

lemma (in Worder) Sup_mem:"\<lbrakk>X \<subseteq> carrier D; \<exists>b. ub X b\<rbrakk> \<Longrightarrow> 
                  Sup D X \<in> carrier D"
apply (frule upper_bounds_sub[of "X"],
       frule minimum_elem_mem[of "upper_bounds D X" "Sup D X"],
       simp add:Sup_def, rule theI')
 apply (rule ex_ex1I)
apply (cut_tac ex_minimum)
apply (frule_tac a = "upper_bounds D X" in forall_spec,
        thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)",
        simp, erule exE)
 apply (rule_tac x = b in nonempty[of _ "upper_bounds D X"],
       simp add:upper_bounds_def, assumption,
       rule_tac ?a1.0 = x and ?a2.0 = y in minimum_elem_unique[of 
         "upper_bounds D X"], assumption+,
       simp add:upper_bounds_def upper_bound_def)
done 

lemma (in Order) S_inductive_sup:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                             minimum_elem D (upper_bounds D X) (Sup D X)"
 apply (simp add:S_inductive_set_def) 
 apply (frule_tac a = X in forall_spec, assumption,
        thin_tac "\<forall>C. Chain D C \<longrightarrow> (\<exists>x\<in>carrier D. minimum_elem D 
                     (upper_bounds D C) x)")
 apply (erule bexE)
 apply (frule Chain_sub[of "X"])
 apply (frule_tac a = x in  Sup[of "X" ], assumption+)
 apply simp
done 

lemma (in Order) adjunct_Chain:"\<lbrakk>Chain D X; b \<in> carrier D; \<forall>x\<in>X. x \<preceq> b\<rbrakk> \<Longrightarrow>
                 Chain D (insert b X)" 
apply (simp add:Chain_def, erule conjE)
apply (frule Torder_adjunction[of X b], assumption+)
apply simp
done

lemma (in Order) S_inductive_sup_mem:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                             Sup D X \<in> carrier D"
apply (frule_tac  X = X in S_inductive_sup, assumption)
apply (simp add:minimum_elem_def, (erule conjE)+,
       simp add:upper_bounds_def, simp add:upper_bound_def)
done

lemma (in Order) S_inductive_Sup_min_bounds:"\<lbrakk>S_inductive_set D; Chain D X;
       ub X b\<rbrakk> \<Longrightarrow>  Sup D X \<preceq> b"
apply (frule S_inductive_sup[of "X"], assumption+,
       simp add:minimum_elem_def, erule conjE)
apply (frule_tac x = b in bspec,
       simp add:upper_bounds_def, assumption)
done

lemma (in Order) S_inductive_sup_bound:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
                                        \<forall>x\<in>X. x \<preceq> (Sup D X)"
apply (frule_tac X = X in S_inductive_sup, assumption+) 
apply (rule ballI)
apply (simp add:minimum_elem_def) apply (erule conjE)
 apply (thin_tac "\<forall>x\<in>upper_bounds D X.  Sup D X \<preceq> x")
 apply (simp add:upper_bounds_def upper_bound_def) 
done

lemma (in Order) S_inductive_Sup_in_ChainTr:
 "\<lbrakk>S_inductive_set D; Chain D X; c \<in> carrier (Iod D (insert (Sup D X) X)); 
  Sup D X \<notin> X;
   \<forall>y\<in>carrier (Iod D (insert (Sup D X) X)). 
    c \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> Sup D X\<rbrakk> \<Longrightarrow> 
    c \<in> upper_bounds D X"
apply (subst upper_bounds_def, simp add:upper_bound_def)
apply (frule Chain_sub[of X],
       frule S_inductive_sup_mem[of X], assumption+,
       frule insert_sub[of X "carrier D" "Sup D X"], assumption)
apply (rule conjI)
 apply (simp add:Iod_carrier,
       frule Chain_sub[of X],
       frule insert_sub[of X "carrier D" "Sup D X"], assumption,
       erule disjE, simp, simp add:subsetD)

apply (rule ballI)
 apply (simp add:Iod_carrier, (erule conjE)+,
        frule S_inductive_sup_bound[of X], assumption+)
 apply (erule disjE, simp)
 apply (frule_tac x = s in bspec, assumption,
        thin_tac "\<forall>y\<in>X. c \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> y \<longrightarrow>
               \<not> y \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> Sup D X",
        frule_tac x = s in bspec, assumption,
        thin_tac "\<forall>x\<in>X. x \<preceq> Sup D X") 
 apply (frule insert_sub[of X "carrier D" "Sup D X"], assumption+,
        cut_tac subset_insertI[of X "Sup D X"],
        frule_tac c = s in subsetD[of X "insert (Sup D X) X"], assumption+,
        frule_tac c = c in subsetD[of X "insert (Sup D X) X"], assumption+,
        frule Iod_Order[of "insert (Sup D X) X"])
 apply (subst Iod_le[THEN sym, of "insert (Sup D X) X"], assumption+,
        rule contrapos_pp, (simp del:insert_subset)+)
 apply (frule Torder_adjunction [of "X" "Sup D X"], assumption+,
        rule S_inductive_sup_bound[of X], assumption+, simp add:Chain_Torder)
 apply (frule_tac a = s and b = c in 
                  Torder.not_le_less[of "Iod D (X \<union> {Sup D X})"])
 apply (simp add:Iod_carrier, simp add:subsetD,
        simp add:Iod_carrier)
 apply (thin_tac "c \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> Sup D X \<longrightarrow>
         \<not> Sup D X \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> Sup D X")
 apply (simp del:insert_sub,
        frule_tac a = s in 
        Torder.not_less_le[of "Iod D (insert (Sup D X) X)" _ "Sup D X"])
 apply (frule insert_sub[of X "carrier D" "Sup D X"], assumption, 
        simp add:Iod_carrier subsetD,
        frule insert_sub[of X "carrier D" "Sup D X"], assumption,
        simp add:Iod_carrier)
 apply simp
 apply (simp add:Iod_le)
 apply (frule_tac c = s in subsetD[of X "carrier D"], assumption+,
        frule_tac a = s and b = "Sup D X" in le_antisym, assumption+)
 apply simp
done   

lemma (in Order) S_inductive_Sup_in_Chain:"\<lbrakk>S_inductive_set D; Chain D X;
       ExPre (Iod D (insert (Sup D X) X)) (Sup D X)\<rbrakk> \<Longrightarrow> Sup D X \<in> X"
apply (frule S_inductive_sup_mem[of X], assumption+)
apply (frule Chain_sub[of X],
       frule insert_sub[of X "carrier D" "Sup D X"], assumption)
apply (rule contrapos_pp, (simp del:insert_subset)+)
 apply (frule Iod_Order[of "insert (Sup D X) X"])
 apply (frule Order.Pre_element[of "Iod D (insert (Sup D X) X)" "Sup D X"])
  apply (simp add:Iod_carrier) apply assumption
  apply ((erule conjE)+, simp del:insert_subset)
  apply (frule S_inductive_Sup_in_ChainTr[of X 
               "Pre (Iod D (insert (Sup D X) X)) (Sup D X)"], assumption+)
  apply (simp add:upper_bounds_def)
  apply (frule S_inductive_Sup_min_bounds[of X 
               "Pre (Iod D (insert (Sup D X) X)) (Sup D X)"], assumption+,
         thin_tac "\<forall>y\<in>carrier (Iod D (insert (Sup D X) X)).
        Pre (Iod D (insert (Sup D X) X)) (Sup D X) \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub>
        y \<longrightarrow>  \<not> y \<prec>\<^bsub>Iod D (insert (Sup D X) X)\<^esub> Sup D X")
  apply (frule Order.less_le_trans[of "Iod D (insert (Sup D X) X)" 
      "Pre (Iod D (insert (Sup D X) X)) (Sup D X)"
      "Sup D X" "Pre (Iod D (insert (Sup D X) X)) (Sup D X)"])
  apply assumption+
  
  apply (frule insert_sub[of X "carrier D" "Sup D X"], assumption,
        simp add:Iod_carrier) apply assumption+
   apply (frule insert_sub[of X "carrier D" "Sup D X"], assumption,
        simp add:Iod_carrier Iod_le) 
   apply (simp add:oless_def)
done

lemma (in Order) S_inductive_bounds_compare:"\<lbrakk>S_inductive_set D; Chain D X1;
       Chain D X2; X1 \<subseteq> X2\<rbrakk> \<Longrightarrow> upper_bounds D X2 \<subseteq> upper_bounds D X1 " 
apply (rule subsetI,
       simp add:upper_bounds_def upper_bound_def,
       erule conjE, rule ballI,
       frule_tac c = s in subsetD[of "X1" "X2"], assumption+) 
 apply simp
done

lemma (in Order) S_inductive_sup_compare:"\<lbrakk>S_inductive_set D; Chain D X1;
       Chain D X2; X1 \<subseteq> X2\<rbrakk> \<Longrightarrow> Sup D X1 \<preceq>  Sup D X2" 
 apply (frule S_inductive_bounds_compare[of "X1" "X2"], assumption+,
        frule Chain_sub[of "X1"], frule Chain_sub[of "X2"],
        frule upper_bounds_sub[of "X1"], frule upper_bounds_sub[of "X2"])
 apply (rule_tac s = "Sup D X2" and t = "Sup D X1" in 
       compare_minimum_elements[of "upper_bounds D X2" "upper_bounds D X1"],
       assumption+,
       simp add:S_inductive_sup, simp add:S_inductive_sup)
done

definition
  Wa :: "[_, 'a set, 'a \<Rightarrow> 'a, 'a] \<Rightarrow> bool" where
  "Wa D W g a \<longleftrightarrow> W \<subseteq> carrier D \<and> Worder (Iod D W) \<and> a \<in> W \<and> (\<forall>x\<in>W. a \<preceq>\<^bsub>D\<^esub> x) \<and> 
    (\<forall>x\<in>W. (if (ExPre (Iod D W) x) then  g (Pre (Iod D W) x) = x else
    (if a \<noteq> x then Sup D (segment (Iod D W) x) = x else a = a)))"

definition 
  WWa :: "[_, 'a \<Rightarrow> 'a, 'a] \<Rightarrow> 'a set set" where
  "WWa D g a = {W. Wa D W g a}"
 
lemma (in Order) mem_of_WWa:"\<lbrakk>W \<subseteq> carrier D; Worder (Iod D W); a \<in> W;
  (\<forall>x\<in>W. a \<preceq> x); 
  (\<forall>x\<in>W. (if (ExPre (Iod D W) x) then  g (Pre (Iod D W) x) = x else
  (if a \<noteq> x then Sup D (segment (Iod D W) x) = x else a = a)))\<rbrakk> \<Longrightarrow>
       W \<in> WWa D g a"
by (simp add:WWa_def, simp add:Wa_def)

lemma (in Order) mem_WWa_then:"W \<in> WWa D g a \<Longrightarrow> W \<subseteq> carrier D \<and> 
  Worder (Iod D W) \<and> a \<in> W \<and> (\<forall>x\<in>W. a \<preceq> x) \<and> 
  (\<forall>x\<in>W. (if (ExPre (Iod D W) x) then  g (Pre (Iod D W) x) = x else
  (if a \<noteq> x then Sup D (segment (Iod D W) x) = x else a = a)))" 
by (simp add:WWa_def Wa_def)
    
lemma (in Order) mem_wwa_Worder:"W \<in> WWa D g a \<Longrightarrow> Worder (Iod D W)"
by (simp add:WWa_def Wa_def)

lemma (in Order) mem_WWa_sub_carrier:"W \<in> WWa D g a \<Longrightarrow> W \<subseteq> carrier D"
by (simp add:WWa_def Wa_def)

lemma (in Order) Union_WWa_sub_carrier:"\<Union> (WWa D g a) \<subseteq> carrier D"
by (rule Union_least[of "WWa D g a" "carrier D"], simp add:mem_WWa_sub_carrier)

lemma (in Order) mem_WWa_inc_a:"W \<in> WWa D g a \<Longrightarrow> a \<in> W"
by (simp add:WWa_def Wa_def)

lemma (in Order) mem_WWa_Chain:"W \<in> WWa D g a \<Longrightarrow> Chain D W"
apply (simp add:Chain_def)
 apply (simp add:mem_WWa_sub_carrier)
 apply (frule mem_wwa_Worder[of "W"])
 apply (simp add:Worder.Torder)
done

lemma (in Order) Sup_adjunct_Sup:"\<lbrakk>S_inductive_set D; 
      f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> f x; 
      W \<in> WWa D f a; Sup D W \<notin> W\<rbrakk>
      \<Longrightarrow> Sup D (insert (Sup D W) W) = Sup D W"
(** use 
             le_antisym
At first applying le_antisym, we see following four items should be proved.
             Sup D W \<in> carrier D
             Sup D (insert (Sup D W) W) \<in> carrier D
             Sup D W \<preceq> Sup D (insert (Sup D W) W)
             Sup D (insert (Sup D W) W) \<preceq> Sup D W
To show Sup D W \<in> carrier D, we apply S_inductive_Sup_mem.     
 **)
apply (frule mem_WWa_Chain[of "W"],
       frule S_inductive_sup_bound[of "W"], assumption,
       frule mem_wwa_Worder[of "W"],
       frule mem_WWa_sub_carrier[of "W"],
       frule S_inductive_sup_mem[of "W"], assumption+) 
apply (frule well_ord_adjunction[of "W" "Sup D W"], assumption+, simp,
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
       frule Worder.Torder[of "Iod D (insert (Sup D W) W)"],
          frule Torder_Chain[of "insert (Sup D W) W"], assumption+,
       frule S_inductive_sup_mem[of "insert (Sup D W) W"], assumption+)
apply (rule le_antisym[of "Sup D (insert (Sup D W) W)" "Sup D W"], assumption+,
       rule S_inductive_Sup_min_bounds[of "insert (Sup D W) W" "Sup D W"],
             assumption+,
       simp add:upper_bound_def, simp add:le_refl)
apply (rule S_inductive_sup_compare[of "W" "insert (Sup D W) W"], assumption+)
apply (simp add:subset_insertI[of "W" "Sup D W"])
done

lemma (in Order) BNTr1:"a \<in> carrier D \<Longrightarrow> Worder (Iod D {a})"
apply intro_locales
apply (frule singleton_sub[of "a" "carrier D"],
       rule Iod_Order[of "{a}"], assumption)
 apply (simp add:Torder_axioms_def)
 apply (rule allI, rule impI)+
 apply (simp add:Iod_carrier, simp add:Iod_le le_refl)
apply (simp add:Worder_axioms_def)
 apply (rule allI, rule impI, erule conjE, simp add:Iod_carrier) 
 apply (frule_tac A = X in nonempty_ex, erule exE,
        frule_tac c = x and A = X and B = "{a}" in subsetD, assumption+,
        simp, 
        frule_tac A = X in singleton_sub[of "a"],
        frule_tac A = X and B = "{a}" in equalityI, assumption+, simp)
apply (simp add:minimum_elem_def Iod_le le_refl)
done
 
lemma (in Order) BNTr2:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; 
                         \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow> {a} \<in> WWa D f a"
apply (simp add:WWa_def Wa_def) 
apply (simp add:Not_ExPre[of "a"])
 apply (simp add:BNTr1 le_refl)
done
 
lemma (in Order) BNTr2_1:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; 
       \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a\<rbrakk> \<Longrightarrow> \<forall>x\<in>W. a \<preceq> x"
by (rule ballI, simp add:WWa_def Wa_def)
     
lemma (in Order) BNTr3:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
       \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a\<rbrakk> \<Longrightarrow> minimum_elem (Iod D W) W a"
(** a \<in> W is required by minimum_elem_def and Iod_le *)
apply (frule mem_WWa_inc_a[of W])
apply (subst minimum_elem_def)
 apply simp
 apply (rule ballI)
 apply (frule mem_WWa_sub_carrier[of W f a])
 apply (frule BNTr2_1[of f a W], assumption+)
 apply (simp add:Iod_le)
done

lemma (in Order) Adjunct_segment_sub:"\<lbrakk>S_inductive_set D; Chain D X\<rbrakk> \<Longrightarrow>
       segment (Iod D (insert (Sup D X) X)) (Sup D X) \<subseteq>  X"
 apply (frule S_inductive_sup_mem[of "X"], assumption+,
        frule Chain_sub[of "X"],
        frule insert_sub[of "X" "carrier D" "Sup D X"], assumption)
apply (rule subsetI)
 apply (simp add:segment_def)
 apply (case_tac "Sup D X \<notin> carrier (Iod D (insert (Sup D X) X))", simp)
 apply (simp add:Iod_carrier)
 
 apply (simp add:Iod_carrier, erule conjE, simp add:oless_def)
done

lemma (in Order) Adjunct_segment_eq:"\<lbrakk>S_inductive_set D; Chain D X;
                Sup D X \<notin> X\<rbrakk> \<Longrightarrow>
       segment (Iod D (insert (Sup D X) X)) (Sup D X) = X"
apply (frule Chain_sub[of "X"],
       frule Adjunct_segment_sub[of "X"], assumption)
apply (rule equalityI, assumption)
apply (frule S_inductive_sup_mem[of "X"], assumption+,
       frule insert_sub[of "X" "carrier D" "Sup D X"], assumption+,
       rule subsetI,
       simp add:segment_def Iod_carrier,
       cut_tac subset_insertI[of "X" "Sup D X"],
       cut_tac insertI1[of "Sup D X" "X"],
       frule_tac c = x in subsetD[of "X" "insert (Sup D X) X"], assumption+)
apply (simp add:Iod_less[of "insert (Sup D X) X"],
       frule S_inductive_sup_bound[of "X"], assumption+,
       frule_tac x = x in bspec, assumption+,
       thin_tac "\<forall>x\<in>X. x \<preceq> Sup D X",
       simp add:oless_def)
apply (rule contrapos_pp, simp+)
done

definition
  fixp :: "['a \<Rightarrow> 'a, 'a] \<Rightarrow> bool" where
  "fixp f a \<longleftrightarrow> f a = a"    (** a is a fixed point of f **)

lemma (in Order) fixp_same:"\<lbrakk>W1 \<subseteq> carrier D; W2 \<subseteq> carrier D; t \<in> W1; 
 b \<in> carrier D; ord_isom (Iod D W1) (Iod (Iod D W2) (segment (Iod D W2) b)) g;
 \<forall>u\<in>segment (Iod D W1) t. fixp g u\<rbrakk> \<Longrightarrow> 
          segment (Iod D W1) t = segment (Iod D W2) (g t)"

 apply (frule Iod_Order[of "W1"],
        frule Iod_Order[of "W2"],
        frule Order.segment_sub[of "Iod D W1" "t"],
        frule Order.segment_sub[of "Iod D W2" "b"],
        frule Order.Iod_Order[of "Iod D W2" "segment (Iod D W2) b"], 
        assumption+)
 apply (frule Order.ord_isom_segment_segment[of "Iod D W1" 
               "Iod (Iod D W2) (segment (Iod D W2) b)" g t], assumption+)
       apply (simp add:Iod_carrier, simp add:Iod_carrier)
       apply (frule Order.ord_isom_mem[of "Iod D W1" 
              "Iod (Iod D W2) (segment (Iod D W2) b)" g t], assumption+,
               simp add:Iod_carrier)
       apply (frule Order.Iod_segment_segment[of "Iod D W2" "g t" b],
                           assumption, simp)
       apply (simp add:Iod_sub_sub[of "segment (Iod D W1) t" W1])
       apply (frule Order.segment_sub [of "Iod (Iod D W2) 
                                        (segment (Iod D W2) b)" "g t"])
       apply (simp add:Iod_sub_sub)
       apply (frule subset_trans[of "segment (Iod D W2) b" W2 "carrier D"],
                     assumption+)
       apply (simp add:Iod_carrier)
       apply (frule Order.segment_sub[of "Iod D W2" "g t"], 
              simp add:Iod_carrier[of W2])
       apply (simp add:Iod_sub_sub[of "segment (Iod D W2) (g t)" W2],
              thin_tac "Iod (Iod D (segment (Iod D W2) b))
                       (segment (Iod D (segment (Iod D W2) b)) (g t)) =
                        Iod D (segment (Iod D W2) (g t))")
       apply (frule subset_trans[of "segment (Iod D W1) t" W1 "carrier D"],
              assumption+,
              frule subset_trans[of "segment (Iod D W2) (g t)" W2 "carrier D"],
              assumption+,
              frule Iod_Order[of "segment (Iod D W1) t"],
              frule Iod_Order[of "segment (Iod D W2) (g t)"])
       apply (thin_tac "segment (Iod D (segment (Iod D W2) b)) (g t) \<subseteq>
                          segment (Iod D W2) b",
              thin_tac "segment (Iod D W2) b \<subseteq> carrier D",
              thin_tac "segment (Iod D W2) (g t) \<subseteq> W2",
              thin_tac "ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g")
apply (rule equalityI)
 apply (rule subsetI) 
 apply (frule_tac a = x in Order.ord_isom_mem[of "Iod D (segment (Iod D W1) t)"
       "Iod D (segment (Iod D W2) (g t))" 
         "restrict g (carrier (Iod D (segment (Iod D W1) t)))"], assumption+,
        simp add:Iod_carrier, simp add:Iod_carrier, simp add:fixp_def)
apply (metis Order.Iod_carrier [OF Order_axioms])
 apply (rule subsetI)
 apply (frule_tac b = x in Order.ord_isom_surj[of 
         "Iod D (segment (Iod D W1) t)" "Iod D (segment (Iod D W2) (g t))" 
         "restrict g (carrier (Iod D (segment (Iod D W1) t)))"]) 
apply assumption
apply (metis Order.Iod_carrier [OF Order_axioms])
apply (metis Order.Iod_carrier [OF Order_axioms] Order.segment_free [OF Order_axioms])
apply (metis Order.Iod_carrier [OF Order_axioms] fixp_def restrict_apply)
done

lemma (in Order) BNTr4_1:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; 
     b \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a;
     ord_isom (Iod D W1) (Iod D (segment (Iod D W2) b)) g\<rbrakk> \<Longrightarrow> 
     \<forall>x\<in>W1. g x = x"
 apply (frule mem_wwa_Worder[of "W1" "f" "a"],
        frule mem_wwa_Worder[of "W2" "f" "a"],
        frule Worder.Order[of "Iod D W2"],
        frule mem_WWa_sub_carrier[of "W2" "f" "a"],
        frule mem_WWa_sub_carrier[of "W1" "f" "a"],
        cut_tac  Worder.segment_Worder[of "Iod D W2" "b"],
        simp add:Worder.Order)
  apply (cut_tac Order.segment_sub[of "Iod D W2" "b"],
                   simp add:Iod_carrier,
         frule subset_trans[of "segment (Iod D W2) b" "W2" "carrier D"],
                   assumption+,
         frule Iod_Order[of "segment (Iod D W2) b"])
  apply (frule Worder.Order[of "Iod D W1"],
         frule Order.ord_isom_onto[of "Iod D W1" 
                      "Iod D (segment (Iod D W2) b)" "g"], assumption+)
  (** transfinite induction **)
  apply (frule Order.ord_isom_minimum[of "Iod D W1" 
         "Iod D (segment (Iod D W2) b)" "g" "W1" "a"], assumption+,
         simp add:Iod_carrier, simp add:Iod_carrier mem_WWa_inc_a,
         simp add:BNTr3)
 apply (frule Order.ord_isom_onto[of "Iod D W1" 
                      "Iod D (segment (Iod D W2) b)" "g"], assumption+,
        simp add:Iod_carrier, frule Worder.Torder[of "Iod D W2"])
 apply (simp add:minimum_elem_sub[THEN sym, of "segment (Iod D W2) b" 
                           "segment (Iod D W2) b"])
      
 apply (simp add:minimum_elem_sub[of "W2" "segment (Iod D W2) b"])
 apply (frule Torder.minimum_segment_of_sub[of "Iod D W2" "W2" "b" "g a"],
        simp add:Iod_carrier, cut_tac subset_self[of "W2"],
        simp add:Iod_sub_sub[of "W2" "W2"],
         thin_tac "minimum_elem (Iod D W2) (segment (Iod D W2) b) (g a)",
        frule BNTr3[of "f" "a" "W2"], assumption+) 
apply (frule Worder.Order[of "Iod D W2"],
        frule Order.minimum_elem_unique[of "Iod D W2" "W2" "g a" "a"],
         simp add:Iod_carrier, assumption+)
 
 apply (simp add:Iod_sub_sub[THEN sym, of "segment (Iod D W2) b" "W2"],
        frule Worder.transfinite_induction[of "Iod D W1" "a" "fixp g"],
        simp add:Iod_carrier, simp add:BNTr3, simp add:fixp_def,
        rule ballI, rule impI)

 apply (frule_tac a = t in Worder_ord_isom_mem[of "Iod D W1" 
          "Iod (Iod D W2) (segment (Iod D W2) b)" "g"], assumption+,
        frule Iod_carrier[THEN sym, of "W2"],
        frule subset_trans[of "segment (Iod D W2) b" "W2" 
                        "carrier (Iod D W2)"], simp,
        thin_tac "W2 = carrier (Iod D W2)",
        simp add:Order.Iod_carrier[of "Iod D W2" "segment (Iod D W2) b"],
        frule_tac c = "g t" in subsetD[of "segment (Iod D W2) b" 
                                   "carrier (Iod D W2)"], assumption+,
        simp add:Iod_carrier)
 apply (case_tac "t = a")
  apply (simp add:fixp_def)
  apply (case_tac "ExPre (Iod D W1) t",
        frule_tac a = t in Worder.ord_isom_Pre1[of "Iod D W1" 
                  "Iod (Iod D W2) (segment (Iod D W2) b)" _ "g"], assumption+,
        simp add:Iod_carrier, assumption+)
  apply (frule_tac a = t in Worder.ord_isom_Pre2[of "Iod D W1"
            "Iod (Iod D W2) (segment (Iod D W2) b)" _ "g"], assumption+,
       simp add:Iod_carrier, assumption+)
  apply (frule_tac a = t in Order.Pre_in_segment[of "Iod D W1"],
        simp add:Iod_carrier, assumption)
  apply (frule_tac x = "Pre (Iod D W1) t" in bspec, assumption,
        thin_tac "\<forall>u\<in>segment (Iod D W1) t. fixp g u") 
       apply (simp add:fixp_def)
  apply (frule_tac a = "g t" in Worder.Pre_segment[of "Iod D W2" _ "b"],
        simp add:Iod_carrier, assumption+)

 apply (rotate_tac -2, frule sym, thin_tac "Pre (Iod D W1) t =
         Pre (Iod (Iod D W2) (segment (Iod D W2) b)) (g t)", simp,
        thin_tac "Pre (Iod (Iod D W2) (segment (Iod D W2) b)) (g t) =
         Pre (Iod D W1) t")
 apply (erule conjE)
 apply (simp add:WWa_def Wa_def, (erule conjE)+,
        thin_tac "\<forall>x\<in>W1. a \<preceq> x", thin_tac "\<forall>x\<in>W2. a \<preceq> x",
        thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x")
 apply (frule_tac x = t in bspec, assumption+,
        thin_tac "\<forall>x\<in>W1.
            if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
            else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x else a = a",
        frule_tac x = "g t" in bspec, assumption+,
        thin_tac "\<forall>x\<in>W2.
            if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
            else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a")
        apply simp
 apply (frule_tac a = t in Worder.ord_isom_Pre11[of "Iod D W1"
                 "Iod (Iod D W2) (segment (Iod D W2) b)" _ "g"], assumption+,
        simp add:Iod_carrier, assumption, simp)

 apply (frule_tac a = "g t" in Worder.segment_Expre[of "Iod D W2" _ "b"],
        assumption, simp,
        thin_tac "\<not> ExPre (Iod (Iod D W2) (segment (Iod D W2) b)) (g t)")
 apply (simp add:WWa_def Wa_def, (erule conjE)+)
 apply (rotate_tac -3,
        frule_tac x = t in bspec, assumption,
        thin_tac "\<forall>x\<in>W1.
            if ExPre (Iod D W1) x then f (Pre (Iod D W1) x) = x
            else if a \<noteq> x then Sup D (segment (Iod D W1) x) = x else a = a")
 apply (rotate_tac 1,
        frule_tac x = "g t" in bspec, assumption,
        thin_tac "\<forall>x\<in>W2.
            if ExPre (Iod D W2) x then f (Pre (Iod D W2) x) = x
            else if a \<noteq> x then Sup D (segment (Iod D W2) x) = x else a = a",
        simp)   
 apply (frule_tac t = t and s = a in not_sym, thin_tac " t \<noteq> a")
 apply (frule_tac b = t in Order.ord_isom_inj[of "Iod D W1" 
                "Iod (Iod D W2) (segment (Iod D W2) b)" "g" "a"], assumption+,
                simp add:Iod_carrier, simp add:Iod_carrier, simp)
 apply (frule_tac t1 = t in fixp_same[THEN sym, of "W1" "W2" _ "b" "g"], 
        assumption+, simp, simp add:fixp_def)
 apply (rule ballI,
        frule_tac x = x in bspec,
        simp add:subsetD[of "W1" "carrier D"], 
        simp add:Iod_carrier fixp_def)
 apply (simp add:Worder.Order, assumption)
done

lemma (in Order) BNTr4_2:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; 
       b \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a;
       ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b))\<rbrakk> \<Longrightarrow> 
       W1 = segment (Iod D W2) b" 
apply (simp add:ord_equiv_def,
       erule exE)
 apply (rename_tac g)
 apply (frule mem_wwa_Worder[of "W1" "f" "a"],
        frule mem_wwa_Worder[of "W2" "f" "a"],
        frule Worder.Order[of "Iod D W2"],
        frule mem_WWa_sub_carrier[of "W2" "f" "a"],
        frule mem_WWa_sub_carrier[of "W1" "f" "a"],
        cut_tac a = b in Worder.segment_Worder[of "Iod D W2"], assumption)
 apply (frule Worder.Order[of "Iod D W1"])
 apply (frule_tac D = "Iod (Iod D W2) (segment (Iod D W2) b)" in  Worder.Order)
 apply (frule Worder.Order[of "Iod D W2"])
 apply (frule_tac a = b in Order.segment_sub[of "Iod D W2"], 
        simp add:Iod_carrier)
 apply (frule_tac A = "segment (Iod D W2) b" in subset_trans[of _ "W2"
         "carrier D"], assumption+)
 apply (frule_tac T = "segment (Iod D W2) b" in Iod_Order)
 apply (frule_tac E = "Iod D (segment (Iod D W2) b)" and f = g in  
        Order.ord_isom_func[of "Iod D W1" ], assumption+)
 apply (frule_tac f = g in Order.ord_isom_onto[of "Iod D W1" 
                            "Iod D (segment (Iod D W2) b)"], assumption+)
 apply (simp only:Iod_carrier)
 apply (frule_tac b = b and g = g in BNTr4_1[of "f" "a" _ "W1" "W2"],
                  assumption+)
 apply (simp add:image_def)
done

lemma (in Order) BNTr4:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D;  a \<in> carrier D; 
       \<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; 
       \<exists>b\<in>carrier D. ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b))\<rbrakk> \<Longrightarrow> 
       W1 \<subseteq> W2" 
apply (erule bexE)
 apply (rename_tac b) 
 apply (frule_tac b = b in BNTr4_2[of "f" "a" _ "W1" "W2"], assumption+)
 apply (frule mem_WWa_sub_carrier[of "W2" "f" "a"],
        frule Iod_Order[of "W2"]) 
 apply (frule_tac a = b in Order.segment_sub[of "Iod D W2"],
        simp add:Iod_carrier)
done

lemma (in Order) Iod_same:"A = B \<Longrightarrow> Iod D A = Iod D B"
by simp

lemma (in Order) eq_ord_equivTr:"\<lbrakk>ord_equiv D E; E = F\<rbrakk> \<Longrightarrow> ord_equiv D F"
by simp

lemma (in Order) BNTr5:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
      \<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a;
      ord_equiv (Iod D W1) (Iod D W2)\<rbrakk> \<Longrightarrow> W1 \<subseteq> W2 " 
 apply (frule mem_WWa_sub_carrier[of "W1" "f" "a"], 
        frule mem_WWa_sub_carrier[of "W2" "f" "a"]) 
 apply (case_tac "W2 = carrier D")
  apply simp
 apply (frule not_sym, thin_tac "W2 \<noteq> carrier D")
 apply (frule sets_not_eq[of "carrier D" "W2"], assumption, erule bexE)
 apply (frule Iod_Order[of "W2"], 
        frule Iod_Order[of "W1"],
        frule Iod_carrier[THEN sym, of "W2"])
        apply (frule_tac a = aa and A = W2 and B = "carrier (Iod D W2)" in 
              eq_set_not_inc, assumption)
        apply (thin_tac "W2 = carrier (Iod D W2)")
  apply (frule_tac a = aa in Order.segment_free[of "Iod D W2"],
          assumption, simp add:Iod_carrier)
  apply (rule BNTr4[of f a W1 W2], assumption+) (** key **)
  apply (frule_tac a = aa in Order.segment_free[of "Iod D W2"])
         apply (simp add:Iod_carrier)
  apply (simp only:Iod_carrier, 
         rotate_tac -1, frule sym, thin_tac "segment (Iod D W2) aa = W2")
  apply (frule_tac B = "segment (Iod D W2) aa" in 
                   Iod_same[of W2])
  apply (frule_tac F = "Iod D (segment (Iod D W2) aa)" in 
         Order.eq_ord_equivTr[of "Iod D W1" "Iod D W2"], assumption+)
  apply blast
done

lemma (in Order) BNTr6:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
\<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; W1 \<subset> W2\<rbrakk> \<Longrightarrow> 
 (\<exists>b\<in>carrier (Iod D W2). ord_equiv (Iod D W1) (Iod D (segment (Iod D W2) b)))"
apply (frule mem_wwa_Worder[of "W1" "f" "a"],
       frule mem_wwa_Worder[of "W2" "f" "a"])
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" in Worder.Word_compare, 
        assumption+) (** key 1 **)
 apply (erule disjE)
  apply (erule bexE,
         frule_tac a = aa in Worder.segment_Worder[of "Iod D W1"],
         frule_tac S = "Iod (Iod D W1) (segment (Iod D W1) aa)" in
           Worder_sym[of _ "Iod D W2"], assumption+,
     thin_tac "ord_equiv (Iod (Iod D W1) (segment (Iod D W1) aa)) (Iod D W2)",
         frule BNTr4[of "f" "a" "W2" "W1"], assumption+,
         frule mem_WWa_sub_carrier[of "W1"],
         simp add:Iod_carrier,
         frule_tac c = aa in subsetD[of "W1" "carrier D"], assumption+,
         frule Iod_Order[of "W1"],
         frule_tac a = aa in Order.segment_sub[of "Iod D W1"],
                  simp add:Iod_carrier)
 apply (frule_tac S = "segment (Iod D W1) aa" and T = W1 in Iod_sub_sub,
                  assumption+, simp, blast)
 apply (simp add:subset_contr[of "W1" "W2"])

apply (erule disjE)
 apply (frule Worder_sym[of "Iod D W1" "Iod D W2"], assumption+,
          thin_tac "ord_equiv (Iod D W1) (Iod D W2)",
        frule BNTr5[of "f" "a" "W2" "W1"], assumption+)
  apply (simp add:subset_contr[of "W1" "W2"])

apply (erule bexE,
       frule mem_WWa_sub_carrier[of "W2"],
       simp add:Iod_carrier,
       frule_tac c = b in subsetD[of "W2" "carrier D"], assumption+,
       frule Iod_Order[of "W2"],
       frule_tac a = b in Order.segment_sub[of "Iod D W2"],
       simp add:Iod_carrier,
       frule_tac S = "segment (Iod D W2) b" and T = W2 in Iod_sub_sub,
                  assumption+, simp) 
 apply blast
done

lemma (in Order) BNTr6_1:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
\<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a; W1 \<subset> W2\<rbrakk> \<Longrightarrow> 
 (\<exists>b\<in>carrier (Iod D W2). W1 = (segment (Iod D W2) b))"
by (frule_tac BNTr6[of "f" "a" "W1" "W2"], assumption+, erule bexE,
       frule mem_WWa_sub_carrier[of "W2"], simp add:Iod_carrier,
       frule_tac c = b in subsetD[of "W2" "carrier D"], assumption+,
       frule_tac b = b in BNTr4_2[of "f" "a" _ "W1" "W2"], assumption+,
       blast)

lemma (in Order) BNTr7:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
      \<forall>x\<in>carrier D. x \<preceq> (f x); W1 \<in> WWa D f a; W2 \<in> WWa D f a\<rbrakk> \<Longrightarrow> 
                W1 \<subseteq> W2 \<or> W2 \<subseteq> W1"
apply (frule mem_wwa_Worder[of "W1" "f" "a"],
       frule mem_wwa_Worder[of "W2" "f" "a"])
 apply (frule_tac D = "Iod D W1" and E = "Iod D W2" in Worder.Word_compare, 
        assumption+)
 apply (erule disjE, erule bexE)  
apply (frule mem_WWa_sub_carrier[of "W1"],
       frule mem_WWa_sub_carrier[of "W2"],
       frule Iod_Order[of "W1"],
       frule Iod_Order[of "W2"],
       frule_tac a = aa in Order.segment_sub[of "Iod D W1"],
                  simp add:Iod_carrier,
       frule_tac S = "segment (Iod D W1) aa" and T = W1 in Iod_sub_sub,
                  assumption+, simp,
       thin_tac "Iod (Iod D W1) (segment (Iod D W1) aa) =
          Iod D (segment (Iod D W1) aa)",
       frule_tac A = "segment (Iod D W1) aa" in subset_trans[of _ "W1" 
          "carrier D"], assumption+,
       frule_tac T = "segment (Iod D W1) aa" in Iod_Order)
      
 apply (frule_tac D = "Iod D (segment (Iod D W1) aa)" in 
           Order.ord_equiv_sym[of _ "Iod D W2"], assumption+)      
 apply (frule_tac c = aa in subsetD[of "W1" "carrier D"], assumption+)
 apply (frule BNTr4[of "f" "a" "W2" "W1"], assumption+, blast, simp)

apply (erule disjE)
 apply (simp add:BNTr5)
 
apply (frule mem_WWa_sub_carrier[of "W2"], simp add:Iod_carrier)
apply (frule BNTr4[of "f" "a" "W1" "W2"], assumption+)
apply (erule bexE,
       frule mem_WWa_sub_carrier[of "W2"],
       simp add:Iod_carrier,
       frule_tac c = b in subsetD[of "W2" "carrier D"], assumption+,
       frule Iod_Order[of "W2"],
       frule_tac a = b in Order.segment_sub[of "Iod D W2"],
       simp add:Iod_carrier,
       frule_tac S = "segment (Iod D W2) b" and T = W2 in Iod_sub_sub,
          assumption+, simp,
       frule_tac c = b in subsetD[of "W2" "carrier D"], assumption+)
apply blast
apply simp
done  

lemma (in Order) BNTr7_1:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
       \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> W; W \<in> WWa D f a; xa \<in> \<Union> (WWa D f a);
         xa \<prec>\<^bsub>Iod D (\<Union> (WWa D f a))\<^esub> x\<rbrakk> \<Longrightarrow> xa \<in> W"
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"],
       frule_tac X = W and C = "WWa D f a" and A = x in UnionI, assumption+,
       simp del:Union_iff add:Iod_less)

 apply (simp only:Union_iff[of "xa" "WWa D f a"], erule bexE, rename_tac W')
 apply (frule_tac ?W1.0 = W and ?W2.0 = W' in BNTr7[of "f" "a"],
           assumption+)
 apply (case_tac "W' \<subseteq> W", simp add:subsetD[of _ "W"])

apply (simp del:Union_iff)
 apply (frule_tac B = W' in psubsetI[of "W"])
 apply (rule not_sym, assumption)
 apply (thin_tac "W \<subseteq> W'", thin_tac "W' \<noteq> W")
 apply (frule_tac ?W2.0 = W' in BNTr6_1[of "f" "a" "W"], assumption+)
 apply (erule bexE)
apply (frule_tac W = W' in mem_WWa_sub_carrier)
       apply (simp add:Iod_carrier)
       apply (frule_tac c = b and A = W' in subsetD[of _ "carrier D"], 
                            assumption+)
  apply (frule_tac W = W' and a = b and y = xa and x = x in segment_inc_less,
          assumption+)
done

lemma (in Order) BNTr7_1_1:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
       \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> W; W \<in> WWa D f a; xa \<in> \<Union> (WWa D f a);
         xa \<prec> x\<rbrakk> \<Longrightarrow> xa \<in> W" 
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"],
       frule Iod_Order[of "\<Union> (WWa D f a)"],
       frule Iod_less[THEN sym, of "\<Union> (WWa D f a)" "xa" "x"], assumption+,
       rule UnionI[of "W" "WWa D f a" "x"], assumption+)
apply (simp del:Union_iff, rule BNTr7_1, assumption+)
done

lemma (in Order) BNTr7_2:" \<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
    \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> \<Union>(WWa D f a); ExPre (Iod D (\<Union>(WWa D f a))) x \<rbrakk>
  \<Longrightarrow> \<forall>W\<in>WWa D f a. (x \<in> W \<longrightarrow> ExPre (Iod D W) x )"
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"])
apply (rule ballI, rule impI)
apply (simp only:ExPre_def)
 apply (erule exE, (erule conjE)+)
 apply (simp only:Iod_carrier)
 apply (frule_tac X = W and C = "WWa D f a" and A = x in UnionI, assumption+)
 apply (simp del:Union_iff)
 apply (frule_tac x = W in bspec, assumption,
        thin_tac "\<forall>y\<in>WWa D f a.
           \<forall>y\<in>y. xa \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> x")
 apply (frule_tac W = W and xa = xa in BNTr7_1[of "f" "a" "x"], assumption+,
        frule_tac W = W in mem_WWa_sub_carrier)
 apply (simp del:Union_iff add:Iod_less)
 apply (subgoal_tac "\<forall>y\<in>W. xa \<prec>\<^bsub>Iod D W\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D W\<^esub> x")
 apply (simp only:Iod_carrier)
 apply (subgoal_tac "xa \<prec>\<^bsub>Iod D W\<^esub> x", blast) 
 apply (simp add:Iod_less)

 apply (rule ballI, rule impI)
 apply (frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>W. xa \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> x",
        frule_tac X = W and C = "WWa D f a" and A = y in UnionI, assumption+)
 apply (simp add:Iod_less)
done

lemma (in Order) BNTr7_3:" \<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
    \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> \<Union>(WWa D f a); ExPre (Iod D (\<Union>(WWa D f a))) x \<rbrakk>
  \<Longrightarrow> \<forall>W\<in>WWa D f a. (x \<in> W \<longrightarrow> Pre (Iod D (\<Union>(WWa D f a))) x = Pre (Iod D W) x)"
apply (rule ballI)
apply (rule impI)
 apply (rule_tac s = "Pre (Iod D W) x" in 
                   sym[of _ "Pre (Iod D (\<Union>(WWa D f a))) x"],
        frule_tac W = W in mem_wwa_Worder,
        frule_tac W = W in mem_WWa_sub_carrier,
        frule BNTr7_2[of "f" "a" "x"], assumption+,
        frule_tac x = W in bspec, assumption,
        thin_tac "\<forall>W\<in>WWa D f a. x \<in> W \<longrightarrow> ExPre (Iod D W) x",
        simp) 
 
 apply (rule_tac D = "Iod D W" and a = x and 
        ?a1.0 = "Pre (Iod D (\<Union>(WWa D f a))) x" in Worder.UniquePre,
        assumption,
        simp add:Iod_carrier, assumption, simp add:Iod_carrier) 
  apply (frule_tac D = "Iod D W" in Worder.Order,
         frule_tac D = "Iod D W" and a = x in Order.Pre_element,
         simp add:Iod_carrier, assumption,
         (erule conjE)+, simp add:Iod_carrier)  
  apply (cut_tac Union_WWa_sub_carrier[of "f" "a"],
         frule Iod_Order[of "\<Union>(WWa D f a)"],
         frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+,
         frule_tac D = "Iod D (\<Union>(WWa D f a))" and a = x in Order.Pre_element,
         simp del:Union_iff add:Iod_carrier, assumption)
 apply (erule conjE)+
 apply (frule_tac W = W and xa = "Pre (Iod D (\<Union>(WWa D f a))) x" in 
        BNTr7_1[of "f" "a" "x"], assumption+,
        simp only:Iod_carrier, assumption,
        simp del:Union_iff)
 
apply (rule conjI,
       simp del:Union_iff add:Iod_carrier Iod_less,
       rule ballI,
       frule_tac X = W and A = y in UnionI[of _ "WWa D f a"], assumption+,
       thin_tac "\<forall>y\<in>W. Pre (Iod D W) x \<prec>\<^bsub>Iod D W\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D W\<^esub> x")
 apply (simp only:Iod_carrier,
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>\<Union>(WWa D f a).
              Pre (Iod D (\<Union>(WWa D f a))) x \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> y \<longrightarrow>
              \<not> y \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> x")
 apply (simp del:Union_iff add:Iod_less)
done

lemma (in Order) BNTr7_4:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
         \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> W;  W \<in> WWa D f a\<rbrakk> \<Longrightarrow> 
         ExPre (Iod D (\<Union>(WWa D f a))) x = ExPre (Iod D W) x"
apply (rule iffI) 
 apply (frule BNTr7_2[of "f" "a" "x"], assumption+)
 apply (frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+,
        simp)
 
apply (simp only:ExPre_def, erule exE, (erule conjE)+)
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"])
apply (frule mem_WWa_sub_carrier[of "W"], simp only:Iod_carrier,
       frule Iod_Order[of "W"]) apply (
       frule Iod_Order[of "\<Union>(WWa D f a)"]) apply (
       simp only:Iod_less)
apply (frule_tac X = W and A = xa in UnionI[of _ "WWa D f a"], assumption+,
       frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+)
 apply (frule_tac T1 = "\<Union>(WWa D f a)" and a1 = xa and b1 = x in 
                                Iod_less[THEN sym], assumption+)
 apply (subgoal_tac " \<not> (\<exists>y\<in>\<Union>(WWa D f a).
                       xa \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> y \<and> y \<prec>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> x)")
 apply blast

 apply (rule contrapos_pp, (simp del:Union_iff)+)
 apply (erule bexE, rename_tac xa W', erule bexE, erule conjE,
        frule_tac X = W' and A = y in UnionI[of _ "WWa D f a"], assumption+)
 apply (frule_tac xa = y in BNTr7_1[of "f" "a" "x" "W"], assumption+)
 apply (frule_tac x = y in bspec, assumption+,
        thin_tac "\<forall>y\<in>W. xa \<prec>\<^bsub>Iod D W\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D W\<^esub> x")
 apply (simp add:Iod_less)
done

lemma (in Order) BNTr7_5:" \<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D;
           \<forall>x\<in>carrier D. x \<preceq> f x; x \<in> W; W \<in> WWa D f a\<rbrakk>
          \<Longrightarrow> (segment (Iod D (\<Union>(WWa D f a))) x) = segment (Iod D W) x"
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"])
apply (frule_tac W = W in mem_WWa_sub_carrier)
apply (frule Iod_Order[of "\<Union>(WWa D f a)"],
       frule Iod_Order[of "W"])
apply (rule equalityI)
 apply (rule subsetI,
       frule Order.segment_sub[of "Iod D (\<Union>(WWa D f a))" "x"],
       frule_tac c = xa in subsetD[of "segment (Iod D (\<Union>(WWa D f a))) x" 
                            "carrier (Iod D (\<Union>(WWa D f a)))"], assumption+,
       frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+)
 apply (frule_tac a1 = xa in Order.segment_inc[THEN sym, 
                             of "Iod D (\<Union>(WWa D f a))" _ "x"],
        assumption, simp add:Iod_carrier, simp del:Union_iff,
        frule_tac xa = xa in BNTr7_1[of "f" "a" "x"], assumption+,
        simp only:Iod_carrier, assumption, simp only:Iod_carrier,
        simp only:Iod_less,
        frule_tac a1 = xa in Iod_less[THEN sym, of "W" _ "x"], 
                   assumption+, simp del:Union_iff,
        subst Order.segment_inc[THEN sym, of "Iod D W" _ "x"], assumption+,
        simp add:Iod_carrier, simp add:Iod_carrier, assumption) 

 apply (rule subsetI,
        frule_tac a1 = xa in Order.segment_inc[THEN sym, of "Iod D W" _ "x"])
 apply (frule Order.segment_sub[of "Iod D W" "x"],
      rule_tac c = xa in subsetD[of "segment (Iod D W) x" "carrier (Iod D W)"],
       assumption+, simp only:Iod_carrier,
      frule_tac W = W in mem_WWa_sub_carrier, frule Iod_Order[of "W"],
      frule Order.segment_sub[of "Iod D W" "x"], simp only:Iod_carrier,
      frule_tac c = xa in subsetD[of "segment (Iod D W) x" "W"],
             simp add:Iod_less)

  apply (frule_tac X = W and A = xa in UnionI[of _ "WWa D f a"], assumption+,
         frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+,
         subst Order.segment_inc[THEN sym, of "Iod D (\<Union>(WWa D f a))" _ "x"],
         assumption+, simp only:Iod_carrier, simp only:Iod_carrier,
         simp only:Iod_less)
done

lemma (in Order) BNTr7_6:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; 
      a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk>  \<Longrightarrow> a \<in> \<Union>(WWa D f a)"
apply (frule BNTr2[of "f" "a"], assumption+,
       frule UnionI[of "{a}" "WWa D f a" "a"]) 
apply (simp, assumption)
done 

lemma (in Order) BNTr7_7:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
      a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); \<exists>xa. Wa D xa f a \<and> x \<in> xa\<rbrakk> \<Longrightarrow> 
      x \<in> \<Union>(WWa D f a)"
apply (subst Union_iff[of "x" "WWa D f a"])
apply (subst WWa_def, blast)
done

lemma (in Order) BNTr7_8:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); \<exists>xa. Wa D xa f a \<and> x \<in> xa\<rbrakk> \<Longrightarrow> x \<in> carrier D"
apply (erule exE) apply (rename_tac W, erule conjE)
 apply (rule_tac A = W and B = "carrier D" and c = x in subsetD,
        rule_tac W = W in mem_WWa_sub_carrier[of _ "f" "a"])
 apply (simp add:WWa_def, assumption)
done 


lemma (in Order) BNTr7_9:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
           \<forall>x\<in>carrier D. x \<preceq> (f x); x \<in> \<Union>(WWa D f a) \<rbrakk> \<Longrightarrow> x \<in> carrier D" 
by (cut_tac Union_WWa_sub_carrier[of "f" "a"],
       rule subsetD[of "\<Union>(WWa D f a)" "carrier D" "x"], assumption+)

lemma (in Order) BNTr7_10:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
      a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a; Sup D W \<notin> W\<rbrakk> \<Longrightarrow>
                \<not> ExPre (Iod D (insert (Sup D W) W)) (Sup D W)"
apply (frule mem_WWa_sub_carrier[of "W" "f" "a"])
apply (frule mem_WWa_Chain[of "W" "f" "a"],
       frule S_inductive_sup_mem[of "W"], assumption+,
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
       cut_tac insertI1[of "Sup D W" "W"],
       cut_tac subset_insertI[of "W" "Sup D W"],
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+)
apply (rule contrapos_pp, simp+)
apply (simp add:ExPre_def)
apply (erule exE, (erule conjE)+)
apply (frule forball_contra[of "carrier (Iod D (insert (Sup D W) W))" _ _ _
       "(=) (Sup D W)"],
       thin_tac "\<forall>y\<in>carrier (Iod D (insert (Sup D W) W)).
            x \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> y \<longrightarrow>
            \<not> y \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> Sup D W")
apply (frule well_ord_adjunction[of "W" "Sup D W"], assumption+,
       simp add:S_inductive_sup_bound[of "W"],
       simp add:mem_wwa_Worder[of "W"],
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
              frule Worder.Torder[of "Iod D (W \<union> {Sup D W})"], simp,
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
              frule Torder_Chain[of "insert (Sup D W) W"], assumption+,
       frule S_inductive_sup_bound[of "insert (Sup D W) W"], assumption+)
       apply (simp only:Iod_carrier)
apply (rule ballI)
apply (rotate_tac -2,
       frule_tac x = y in bspec, assumption+,
       thin_tac "\<forall>x\<in>insert (Sup D W) W. x \<preceq> Sup D (insert (Sup D W) W)",
       cut_tac insertI1[of "Sup D W" "W"],
       simp only:Iod_less)
apply (simp add:Sup_adjunct_Sup, erule disjE)
      apply (frule sym, thin_tac "y = Sup D W", simp)
      apply (frule_tac c = y in subsetD[of "W" "carrier D"], assumption+)  
apply (frule_tac a = y and b = "Sup D W" in le_imp_less_or_eq, assumption+,
       simp) apply (
       thin_tac "y \<preceq> Sup D W",
       thin_tac "x = Sup D W \<or> x \<in> W")
       apply (erule disjE, simp, simp)

apply (thin_tac "\<forall>y\<in>carrier (Iod D (insert (Sup D W) W)).
            x \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> y \<longrightarrow>
            \<not> y \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> Sup D W")
apply (frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
       cut_tac insertI1[of "Sup D W" "W"],
       simp only:Iod_carrier Iod_less) 
apply (frule mem_wwa_Worder[of "W"],
       frule S_inductive_sup_bound[of "W"], assumption+,
       frule well_ord_adjunction[of "W" "Sup D W"], assumption+,
       frule Worder.Torder[of "Iod D (W \<union> {Sup D W})"], simp)
apply (frule forball_contra1,
       thin_tac "\<forall>y\<in>W. x \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> y \<longrightarrow> Sup D W = y")
apply (rule ballI)
 apply (rule contrapos_pp, simp+)
 apply (frule_tac b = x in S_inductive_Sup_min_bounds[of "W"], assumption+)
 apply (simp add:upper_bound_def)
 apply (erule disjE, simp add:oless_def)
 apply (simp add:subsetD[of "W" "carrier D"])
 apply (rule ballI)
 apply (thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
        thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W")
 apply (frule_tac x = s in bspec, assumption+,
        thin_tac "\<forall>y\<in>W. \<not> x \<prec>\<^bsub>Iod D (insert (Sup D W) W)\<^esub> y")
 apply (frule_tac c = x in subsetD[of "W" "insert (Sup D W) W"], assumption+,
        frule_tac c = s in subsetD[of "W" "insert (Sup D W) W"], assumption+)
 apply (simp add:Iod_not_less_le Iod_le)
 apply (erule disjE, simp add:oless_def,
        frule_tac c = x in subsetD[of "W" "insert (Sup D W) W"], assumption+,
        cut_tac insertI1[of "Sup D W" "W"],
        frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+)
 apply (frule_tac a1 = "Sup D W" and b1 = x in Iod_le[THEN sym, 
                   of "insert (Sup D W) W"], assumption+, simp)
 apply (frule_tac c = x in subsetD[of "W" "insert (Sup D W) W"], assumption+,
        cut_tac insertI1[of "Sup D W" "W"],
        frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+)
 apply (simp only:Iod_not_less_le[THEN sym])
 apply (frule_tac c = x in subsetD[of "W" "insert (Sup D W) W"], assumption+,
        cut_tac insertI1[of "Sup D W" "W"],
        frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+)
 apply (simp add:Iod_less)
done 

lemma (in Order) BNTr7_11:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
 a \<in> carrier D; b \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> f x; W \<in> WWa D f a; 
 \<forall>x\<in>W. x \<preceq> b; x \<in> W\<rbrakk> \<Longrightarrow>
 ExPre (Iod D (insert b W)) x = ExPre (Iod D W) x"
apply (case_tac "b \<in> W",
         simp add:insert_absorb[of "b" "W"])
apply (frule mem_WWa_sub_carrier[of "W"],
       frule subsetD[of "W" "carrier D" "x"], assumption+,
       frule mem_wwa_Worder[of "W"],
       frule mem_WWa_Chain[of "W" "f" "a"],
       frule well_ord_adjunction[of "W" "b"], assumption+,
       frule insert_sub[of "W" "carrier D" "b"], assumption+,
       cut_tac insertI1[of "b" "W"],
       cut_tac subset_insertI[of "W" "b"])
apply (simp del:insert_iff insert_subset add:Un_commute,
       frule Worder.Torder[of "Iod D (insert b W)"])
apply (rule iffI)
 apply (frule subsetD[of "W" "insert b W" "x"], assumption+,
        frule Iod_Order[of "insert b W"],
        unfold ExPre_def)
 apply (erule exE, (erule conjE)+)
 apply (rule contrapos_pp, (simp del:insert_iff insert_subset)+)
 apply (frule_tac a = xa in forall_spec,
        thin_tac "\<forall>xa. xa \<prec>\<^bsub>Iod D W\<^esub> x \<longrightarrow> xa \<in> carrier (Iod D W) \<longrightarrow>
               (\<exists>y\<in>carrier (Iod D W). xa \<prec>\<^bsub>Iod D W\<^esub> y \<and> y \<prec>\<^bsub>Iod D W\<^esub> x)")
 apply (simp only:Iod_carrier)
 apply (simp del:insert_subset) apply (cut_tac insertI1[of "b" "W"])
 apply (erule disjE) apply (simp del:insert_iff insert_subset)
 apply (thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x")
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>W. x \<preceq> b")
 apply (frule subsetD[of "W" "insert b W" "x"], assumption+,
        frule Iod_carrier[THEN sym, of "insert b W"], 
        frule eq_set_inc[of "x" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        frule eq_set_inc[of "b" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        frule Torder.not_le_less[THEN sym, of "Iod D (insert b W)" "x" "b"], 
                      assumption+,
        thin_tac "insert b W = carrier (Iod D (insert b W))")
  apply (simp del:insert_iff insert_subset add:Iod_le)
  apply (frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
         frule subsetD[of "W" "insert b W" "x"], assumption+,
         simp only:Iod_less, simp only:Iod_carrier)
  apply (cut_tac a = xa in insert_iff[of _ "b" "W"],
          simp del:insert_iff insert_subset)
  apply (erule disjE)
  apply (frule Iod_carrier[THEN sym, of "insert b W"])
  apply (frule_tac a = b in eq_set_inc[of _ "insert b W" 
                     "carrier (Iod D (insert b W))"], assumption+,
         frule_tac a = x in eq_set_inc[of _ "insert b W" 
                     "carrier (Iod D (insert b W))"], assumption+,
         thin_tac "insert b W = carrier (Iod D (insert b W))")
  apply (simp del:insert_iff insert_subset add:Torder.not_le_less[THEN sym, 
           of "Iod D (insert b W)" "x" "b"])
  apply (rotate_tac 5,
         frule_tac x = x in bspec, assumption,
         thin_tac "\<forall>x\<in>W. x \<preceq> b", simp add:Iod_le)
  apply (thin_tac "xa \<in> insert b W", erule conjE,
         simp del:insert_iff insert_subset,
         thin_tac "\<forall>xa. xa \<prec>\<^bsub>Iod D W\<^esub> x \<longrightarrow>
               xa \<in> W \<longrightarrow> (\<exists>y\<in>W. xa \<prec>\<^bsub>Iod D W\<^esub> y \<and> y \<prec>\<^bsub>Iod D W\<^esub> x)")
  apply (erule bexE, erule conjE)
  apply (thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
         thin_tac "\<forall>x\<in>W. x \<preceq> b",
         frule_tac x = y in bspec, assumption,
         thin_tac "\<forall>y\<in>W. xa \<prec>\<^bsub>Iod D (insert b W)\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D (insert b W)\<^esub> x",
         frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
         frule_tac c = y in subsetD[of "W" "insert b W"], assumption+)
  apply (simp del:insert_iff insert_subset add:Iod_less)

apply (erule exE, (erule conjE)+)
 apply (rule contrapos_pp, (simp del:insert_iff insert_subset)+)
 apply (frule_tac a = xa in forall_spec,
        simp only:Iod_carrier,
        frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
        frule_tac c = x in subsetD[of "W" "insert b W"], assumption+,
        simp add:Iod_less)
 apply (simp only:Iod_carrier,
        frule_tac c = xa in subsetD[of "W" "insert b W"], assumption,
        simp del:insert_iff insert_subset add:Iod_less)
 apply (erule disjE, erule conjE) apply (
        frule_tac a = xa in forall_spec,
        thin_tac "\<forall>xa. xa \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<longrightarrow> xa \<in> insert b W \<longrightarrow>
       xa \<prec> b \<and> b \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<or> (\<exists>y\<in>W. xa \<prec> y \<and> y \<prec>\<^bsub>Iod D (insert b W)\<^esub> x)")
 apply (thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>W. x \<preceq> b",
        frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+, 
        frule_tac c = x in subsetD[of "W" "insert b W"], assumption+,
        simp only:Iod_less)
 apply (thin_tac "\<forall>xa. xa \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<longrightarrow> xa \<in> insert b W \<longrightarrow>
       xa \<prec> b \<and> b \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<or> (\<exists>y\<in>W. xa \<prec> y \<and> y \<prec>\<^bsub>Iod D (insert b W)\<^esub> x)")
 apply (simp del:insert_iff insert_subset)
 apply (thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>W. x \<preceq> b",
        frule_tac subsetD[of "W" "insert b W" "x"], assumption+,
        frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
        frule Iod_carrier[THEN sym, of "insert b W"], 
        frule eq_set_inc[of "x" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        frule eq_set_inc[of "b" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        frule Torder.not_le_less[THEN sym, of "Iod D (insert b W)" "x" "b"], 
                      assumption+,
        thin_tac "insert b W = carrier (Iod D (insert b W))",
        simp add:Iod_le,
        thin_tac "\<forall>xa. xa \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<longrightarrow> xa \<in> insert b W \<longrightarrow>
      xa \<prec> b \<and> b \<prec>\<^bsub>Iod D (insert b W)\<^esub> x \<or> (\<exists>y\<in>W. xa \<prec> y \<and> y \<prec>\<^bsub>Iod D (insert b W)\<^esub> x)")
 apply (erule bexE, erule conjE,
        thin_tac "\<forall>x\<in>W. x \<preceq> b",
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>W. xa \<prec> y \<longrightarrow> \<not> y \<prec> x",
        frule_tac c = y in subsetD[of "W" "insert b W"], assumption+,
        frule_tac c = x in subsetD[of "W" "insert b W"], assumption+,
        simp add:Iod_less)
done

lemma (in Order) BNTr7_12:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
 a \<in> carrier D; b \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> f x; W \<in> WWa D f a; 
 \<forall>x\<in>W. x \<preceq> b; x \<in> W; ExPre (Iod D W) x\<rbrakk> \<Longrightarrow> 
        Pre (Iod D (insert b W)) x = Pre (Iod D W) x"
apply (case_tac "b \<in> W", simp only:insert_absorb)
apply (frule mem_WWa_Chain[of "W"], 
       frule mem_wwa_Worder[of "W"],
       frule mem_WWa_sub_carrier[of "W"],
       frule well_ord_adjunction[of "W" "b"], assumption+,
       simp add:Un_commute[of "W" "{b}"],
       frule insert_sub[of "W" "carrier D" "b"], assumption+,
       cut_tac subset_insertI[of "W" "b"],
       frule subsetD[of "W" "insert b W" "x"], assumption+,
       cut_tac insertI1[of "b" "W"])
apply (rule Worder.UniquePre[of "Iod D (insert b W)" "x" 
                    "Pre (Iod D W) x"], assumption+,
       simp add:Iod_carrier,
       subst BNTr7_11[of "f" "a" "b" "W" "x"], assumption+,
       frule Worder.Order[of "Iod D W"]) 
apply (frule Order.Pre_element[of "Iod D W" "x"],
       simp add:Iod_carrier, assumption)
apply (erule conjE)+
apply (rule conjI)
apply (simp add:Iod_carrier) 
apply (rule conjI)
 apply (simp only:Iod_carrier,
        frule subsetD[of "W" "insert b W" "x"], assumption+,
        frule subsetD[of "W" "insert b W" "Pre (Iod D W) x"], 
        assumption+)
 apply (simp only:Iod_less)
apply (rule contrapos_pp, (simp del:insert_iff insert_subset)+)
 apply (erule bexE) 
 apply (simp only:Iod_carrier,
        frule subsetD[of "W" "insert b W" "Pre (Iod D W) x"], 
        assumption+)
 apply (cut_tac a = y in insert_iff[of _ "b" "W"]) 
 apply (frule_tac P = "y \<in> insert b W" and Q = "y = b \<or> y \<in> W" in 
        eq_prop, assumption+,
        thin_tac "(y \<in> insert b W) = (y = b \<or> y \<in> W)",
        thin_tac "y \<in> insert b W")
 apply (erule disjE,
        thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>W. x \<preceq> b", erule conjE,
        frule Iod_carrier[THEN sym, of "insert b W"],
        frule eq_set_inc[of "x" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        frule eq_set_inc[of "b" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
        thin_tac "insert b W = carrier (Iod D (insert b W))",
        simp del:insert_iff insert_subset,
        frule Worder.Torder[of "Iod D (insert b W)"],
         frule Torder.not_le_less[THEN sym, of "Iod D (insert b W)" "x" "b"], 
                      assumption+, simp add:Iod_le)
 apply (rotate_tac -4,
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>W. Pre (Iod D W) x \<prec>\<^bsub>Iod D W\<^esub> y \<longrightarrow> \<not> y \<prec>\<^bsub>Iod D W\<^esub> x",
        frule_tac c = y in subsetD[of "W" "insert b W"], assumption,
        simp add:Iod_less) 
done
        
lemma (in Order) BNTr7_13:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
   a \<in> carrier D; b \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> f x; W \<in> WWa D f a; 
   \<forall>x\<in>W. x \<preceq> b; x \<in> W\<rbrakk> \<Longrightarrow> 
        (segment (Iod D (insert b W)) x) = segment (Iod D W) x"
apply (case_tac "b \<in> W", simp add:insert_absorb)
apply (frule mem_wwa_Worder[of "W"],
       frule mem_WWa_sub_carrier[of "W"],
       frule mem_WWa_Chain[of "W"],
       frule insert_sub[of "W" "carrier D" "b"], assumption+,
       frule well_ord_adjunction[of "W" "b"], assumption+,
       simp del:insert_subset add:Un_commute,
       cut_tac subset_insertI[of "W" "b"],
       cut_tac insertI1[of "b" "W"],
       frule Worder.Torder[of "Iod D (insert b W)"])
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp del:insert_iff insert_subset add:segment_def Iod_carrier)
 apply (frule subsetD[of "W" "insert b W" "x"], assumption+,
        simp del:insert_iff insert_subset)
 apply (erule conjE, simp only:Iod_carrier)
 apply (cut_tac a = xa in insert_iff[of _ "b" "W"],
        frule_tac P = "xa \<in> insert b W" and Q = "xa = b \<or> xa \<in> W" in 
        eq_prop, assumption+) 
apply (thin_tac "(xa \<in> insert b W) = (xa = b \<or> xa \<in> W)",
       erule disjE, simp del:insert_iff insert_subset,
       frule Iod_carrier[THEN sym, of "insert b W"], 
       frule eq_set_inc[of "x" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
       frule eq_set_inc[of "b" "insert b W" "carrier (Iod D (insert b W))"],
                      assumption,
       thin_tac "insert b W = carrier (Iod D (insert b W))",
       frule Torder.not_le_less[THEN sym, of "Iod D (insert b W)" "x" "b"],
       assumption+, simp add:Iod_le)
apply (frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
       frule_tac c = x in subsetD[of "W" "insert b W"], assumption+,
       simp add:Iod_less)

apply (rule subsetI)
 apply (simp del:insert_iff insert_subset add:segment_def,
        simp only:Iod_carrier)
 apply (frule_tac subsetD[of "W" "insert b W" "x"], assumption+,
        simp del:insert_iff insert_subset)
 apply (erule conjE,
        frule_tac c = xa in subsetD[of "W" "insert b W"], assumption+,
        simp add:Iod_less)
done


lemma (in Order) BNTr7_14:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
      a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a\<rbrakk> \<Longrightarrow>
            (insert (Sup D W) W) \<in> WWa D f a"
apply (case_tac "Sup D W \<in> W",
       simp add:insert_absorb[of "Sup D W" "W"])
apply (frule mem_WWa_sub_carrier[of "W" "f" "a"],
       frule mem_WWa_Chain[of "W" "f" "a"],
       frule S_inductive_sup_mem[of "W"], assumption+,
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+,
       rule mem_of_WWa [of "insert (Sup D W) W" "a" "f"], assumption+,
       frule S_inductive_sup_bound[of "W"], assumption+)
apply (frule well_ord_adjunction[of "W" "Sup D W"], assumption+,
       simp add:mem_wwa_Worder, simp,
       frule mem_WWa_inc_a[of "W" "f" "a"], simp)

apply (rule ballI)
 apply (simp add:WWa_def Wa_def, (erule conjE)+, erule disjE,
        frule S_inductive_sup_bound[of "W"], assumption+,
        simp, simp)

apply (rule ballI)
 apply (simp only:insert_iff)
 apply (erule disjE)
 apply (frule mem_WWa_inc_a[of "W" "f" "a"])
 apply (frule not_eq_outside [of "Sup D W" "W"])
 apply (rotate_tac -1, 
       frule_tac x = a in bspec, assumption+,
       thin_tac "\<forall>b\<in>W. b \<noteq> Sup D W")
 apply (frule BNTr7_10[of "f" "a" "W"], assumption+)
 apply (simp del:insert_iff insert_subset add:Adjunct_segment_eq)
 apply (frule S_inductive_sup_bound[of "W"], assumption+)
 apply (subst BNTr7_11[of "f" "a" "Sup D W" "W"], assumption+)
 apply (case_tac "ExPre (Iod D W) x",
        subst BNTr7_12[of "f" "a" "Sup D W" "W"], assumption+)
 apply (simp del:insert_iff insert_subset add:WWa_def) 
 apply (unfold Wa_def, simp)
 apply (simp del:insert_iff insert_subset)
 apply (rule impI) 
 apply (subst BNTr7_13[of "f" "a" "Sup D W" "W"], assumption+)
 apply (simp add:WWa_def Wa_def)
done

lemma (in Order) BNTr7_15:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
     a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a;
     f (Sup D W) \<noteq> Sup D W\<rbrakk> \<Longrightarrow>
     ExPre (Iod D (insert (f (Sup D W)) (insert (Sup D W) W))) (f (Sup D W))"
apply (simp add:ExPre_def)
apply (rule contrapos_pp, simp+)
apply (frule BNTr7_14[of "f" "a" "W"], assumption+)
apply (frule mem_WWa_sub_carrier[of "insert (Sup D W) W" "f" "a"],
      frule mem_WWa_Chain[of "insert (Sup D W) W" "f" "a"],
      frule mem_wwa_Worder[of "insert (Sup D W) W" "f" "a"],
      frule mem_WWa_Chain[of "W" "f" "a"],
      frule S_inductive_sup_mem[of "W"], assumption+,
      frule funcset_mem[of "f" "carrier D" "carrier D" "Sup D W"], assumption+,
      frule insert_sub[of "insert (Sup D W) W" "carrier D" "f (Sup D W)"], 
         assumption+,
      frule S_inductive_sup_bound[of "W"], assumption+)
apply (frule well_ord_adjunction[of "insert (Sup D W) W" "f (Sup D W)"], 
       assumption+,
       rule ballI,
       simp only:insert_iff, erule disjE, simp del:insert_iff insert_subset)
apply (frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x") apply (
       rotate_tac -3,
       frule_tac x = x in bspec, assumption,
       thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W") apply (
       frule mem_WWa_sub_carrier[of "W"],
       frule_tac c = x in subsetD[of "W" "carrier D"], assumption+,
       rule_tac a = x in le_trans[of _ "Sup D W" "f (Sup D W)"], assumption+,
       cut_tac insertI1[of "Sup D W" "W"],
       cut_tac insertI1[of "f (Sup D W)" "insert (Sup D W) W"],
       cut_tac subset_insertI[of "insert (Sup D W) W" "f (Sup D W)"],
       frule subsetD[of "insert (Sup D W) W" "insert (f (Sup D W)) 
               (insert (Sup D W) W)" "Sup D W"], assumption+)
apply (frule_tac a = "Sup D W" in forall_spec)
apply (frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
       frule not_sym, 
       thin_tac "f (Sup D W) \<noteq> Sup D W",
       simp del:insert_iff insert_subset 
             add:le_imp_less_or_eq[of "Sup D W" "f (Sup D W)"],
       simp only:Iod_less) 
apply (thin_tac "\<forall>x. x \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> f (Sup D W) \<longrightarrow>
         x \<in> carrier (Iod D (insert (f (Sup D W)) (insert (Sup D W) W))) \<longrightarrow>
         (\<exists>y\<in>carrier (Iod D (insert (f (Sup D W)) (insert (Sup D W) W))).
             x \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> y \<and>
             y \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub>
             f (Sup D W))",
      simp only:Iod_carrier,
      frule True_then[of "\<exists>y\<in>insert (f (Sup D W)) (insert (Sup D W) W).
         Sup D W \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> y \<and>
         y \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> f (Sup D W)"],
      thin_tac "True \<longrightarrow>
      (\<exists>y\<in>insert (f (Sup D W)) (insert (Sup D W) W).
         Sup D W \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> y \<and>
         y \<prec>\<^bsub>Iod D (insert (f (Sup D W)) (insert (Sup D W) W))\<^esub> f (Sup D W))",
       erule bexE, erule conjE)
apply (cut_tac a = y in insert_iff[of _ "f (Sup D W)" "insert (Sup D W) W"],
       frule_tac P = "y \<in> insert (f (Sup D W)) (insert (Sup D W) W)" and
                 Q = "y = f (Sup D W) \<or> y \<in> insert (Sup D W) W" in eq_prop,
       assumption+,
       thin_tac "y \<in> insert (f (Sup D W)) (insert (Sup D W) W)",
       thin_tac "(y \<in> insert (f (Sup D W)) (insert (Sup D W) W)) =
         (y = f (Sup D W) \<or> y \<in> insert (Sup D W) W)")
apply (erule disjE, simp add:oless_def)
apply (cut_tac a = y in insert_iff[of _ "Sup D W" "W"],
       frule_tac P = "y \<in> insert (Sup D W) W" and
                 Q = "y = (Sup D W) \<or> y \<in> W" in eq_prop, assumption+,
       thin_tac "y \<in> insert (Sup D W) W",
       thin_tac "y \<in> insert (Sup D W) W = (y = (Sup D W) \<or> y \<in> W)",
       erule disjE, simp add:oless_def,
       simp del:insert_iff insert_subset)
apply (frule_tac x = y in bspec, assumption,
       thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W")
apply (frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
       cut_tac subset_insertI[of "W" "Sup D W"],
       frule_tac c = y in subsetD[of "W" "insert (Sup D W) W"], assumption+,
       frule_tac c = y in subsetD[of "insert (Sup D W) W"
                  "insert (f (Sup D W)) (insert (Sup D W) W)"], assumption+,
       frule_tac Worder.Torder[of "Iod D (insert (f (Sup D W)) 
                                         (insert (Sup D W) W))"])
apply (frule_tac a1 = y in Torder.not_le_less[THEN sym, of 
       "Iod D (insert (f (Sup D W)) (insert (Sup D W) W))" _ "Sup D W"],
       simp add:Iod_carrier, simp add:Iod_carrier)
apply (simp add:Iod_le)
done
       
lemma (in Order) BNTr7_16:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
     a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a; 
     f (Sup D W) \<noteq> (Sup D W)\<rbrakk> \<Longrightarrow>
     Pre (Iod D (insert (f (Sup D W)) (insert (Sup D W) W))) (f (Sup D W)) = 
          (Sup D W)" 
apply (frule BNTr7_14[of "f" "a" "W"], assumption+,
      frule mem_WWa_sub_carrier[of "insert (Sup D W) W" "f" "a"],
      frule mem_WWa_Chain[of "insert (Sup D W) W" "f" "a"],
      frule mem_wwa_Worder[of "insert (Sup D W) W" "f" "a"],
      frule mem_WWa_Chain[of "W" "f" "a"],
      frule S_inductive_sup_mem[of "W"], assumption+,
      frule funcset_mem[of "f" "carrier D" "carrier D" "Sup D W"], assumption+,
      frule insert_sub[of "insert (Sup D W) W" "carrier D" "f (Sup D W)"], 
         assumption+,
      frule S_inductive_sup_bound[of "W"], assumption+,
      frule well_ord_adjunction[of "insert (Sup D W) W" "f (Sup D W)"], 
      assumption+, rule ballI,
      simp only:insert_iff, erule disjE, simp del:insert_iff insert_subset,
      frule_tac x = "Sup D W" in bspec, assumption,
      thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
      rotate_tac -3,
      frule_tac x = x in bspec, assumption,
      thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
      frule mem_WWa_sub_carrier[of "W"],
      frule_tac c = x in subsetD[of "W" "carrier D"], assumption+,
      rule_tac a = x in le_trans[of _ "Sup D W" "f (Sup D W)"], assumption+,
      cut_tac insertI1[of "Sup D W" "W"],
      cut_tac insertI1[of "f (Sup D W)" "insert (Sup D W) W"],
      cut_tac subset_insertI[of "insert (Sup D W) W" "f (Sup D W)"],
      frule subsetD[of "insert (Sup D W) W" "insert (f (Sup D W)) 
               (insert (Sup D W) W)" "Sup D W"], assumption+)
   apply (simp only:Un_commute[of "insert (Sup D W) W" "{f (Sup D W)}"],
          simp only:insert_is_Un[THEN sym])
apply (rule Worder.UniquePre[of "Iod D (insert (f (Sup D W)) 
       (insert (Sup D W) W))" "f (Sup D W)" "Sup D W"], assumption+,
       simp only:Iod_carrier,
       rule BNTr7_15, assumption+,
       rule conjI, simp only:Iod_carrier, rule conjI, simp only:Iod_less,
       frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x", frule not_sym, 
       thin_tac "f (Sup D W) \<noteq> Sup D W", simp add:oless_def) 
apply (rule contrapos_pp, (simp del:insert_iff insert_subset)+,
       erule bexE, erule conjE)
       apply (simp only:Iod_carrier) apply (
       cut_tac a = y in insert_iff[of _ "f (Sup D W)" "insert (Sup D W) W"],
       frule_tac P = "y \<in> insert (f (Sup D W)) (insert (Sup D W) W)" and 
        Q = "y = f (Sup D W) \<or> y \<in> insert (Sup D W) W" in eq_prop,
        assumption,
       thin_tac "y \<in> insert (f (Sup D W)) (insert (Sup D W) W)",
       thin_tac "y \<in> insert (f (Sup D W)) (insert (Sup D W) W) =
                (y = f (Sup D W) \<or> y \<in> insert (Sup D W) W)",
       erule disjE, simp add:oless_def) apply (
       cut_tac a = y in insert_iff[of _ "Sup D W" "W"],
       frule_tac P = "y \<in> insert (Sup D W) W" and 
        Q = "y = (Sup D W) \<or> y \<in> W" in eq_prop, assumption,
       thin_tac "y \<in> insert (Sup D W) W",
       thin_tac "y \<in> (insert (Sup D W) W) = (y = (Sup D W) \<or> y \<in> W)",
       erule disjE, simp add:oless_def)
apply (frule_tac x = y in bspec, assumption,
       thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
       cut_tac subset_insertI[of "W" "Sup D W"],
       frule_tac c = y in subsetD[of "W" "insert (Sup D W) W"], assumption,
       frule Worder.Torder[of "Iod D (insert (f (Sup D W)) 
                                     (insert (Sup D W) W))"]) 
apply (frule mem_WWa_sub_carrier[of "W"],
       frule_tac c = y in subsetD[of "W" "carrier D"], assumption+,
       frule_tac c = y in subsetD[of "insert (Sup D W) W" 
             "insert (f (Sup D W)) (insert (Sup D W) W)"], assumption+,
       frule_tac a1 = y in Torder.not_le_less[THEN sym, 
        of "Iod D (insert (f (Sup D W)) (insert (Sup D W) W))" _ "Sup D W"],
       simp add:Iod_carrier, simp add:Iod_carrier)
      apply (simp add:Iod_le)
done

lemma (in Order) BNTr7_17:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
      a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a\<rbrakk> \<Longrightarrow>
          (insert (f (Sup D W)) (insert (Sup D W) W)) \<in> WWa D f a"
apply (frule mem_WWa_Chain[of "W"],
       frule S_inductive_sup_mem[of "W"], assumption+)
apply (case_tac "f (Sup D W) = Sup D W",
       simp add:insert_absorb, simp add: BNTr7_14,
       frule not_sym, thin_tac "f (Sup D W) \<noteq> Sup D W")
apply (frule BNTr7_14[of "f" "a" "W"], assumption+,
      frule mem_WWa_sub_carrier[of "insert (Sup D W) W" "f" "a"],
      frule mem_WWa_Chain[of "insert (Sup D W) W" "f" "a"],
      frule funcset_mem[of "f" "carrier D" "carrier D" "Sup D W"], assumption+,
      frule mem_wwa_Worder[of "insert (Sup D W) W"])
apply (frule insert_sub[of "insert (Sup D W) W" "carrier D" "f (Sup D W)"], 
        assumption+,
       rule mem_of_WWa [of "(insert (f (Sup D W)) (insert (Sup D W) W))" "a"
        "f"], assumption+)
apply (frule well_ord_adjunction[of "insert (Sup D W) W" "f (Sup D W)"],
        assumption+, 
       frule S_inductive_sup_bound[of "W"], assumption+,
             rule ballI, 
             simp only:insert_iff, erule disjE, simp,
       frule_tac x = x in bspec, assumption,
             thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
       frule_tac x = "Sup D W" in bspec, assumption,
             thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
       frule mem_WWa_sub_carrier[of "W"],
       frule_tac c = x in subsetD[of "W" "carrier D"], assumption+,
       rule_tac a = x in le_trans[of _ "Sup D W" "f (Sup D W)"], 
             assumption+, simp)
apply (frule mem_WWa_inc_a[of "insert (Sup D W) W" "f" "a"],
       simp)
apply (rule ballI) 
 apply (frule BNTr2_1[of "f" "a" "insert (Sup D W) W"], assumption+,
        cut_tac a = x in insert_iff[of _ "f (Sup D W)" "insert (Sup D W) W"],
        frule_tac P = "x \<in> insert (f (Sup D W)) (insert (Sup D W) W)" and 
         Q = "x = (f (Sup D W)) \<or> x \<in> (insert (Sup D W) W)" in eq_prop, 
                             assumption+,
        thin_tac "x \<in> insert (f (Sup D W)) (insert (Sup D W) W)",  
        thin_tac "(x \<in> insert (f (Sup D W)) (insert (Sup D W) W)) =
         (x = f (Sup D W) \<or> x \<in> insert (Sup D W) W)",
        erule disjE)
 apply (frule_tac x = "Sup D W" in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
        frule_tac x = "Sup D W" in bspec, simp) 
apply (
        thin_tac "\<forall>x\<in>insert (Sup D W) W. a \<preceq> x",
        simp add:le_trans[of "a" "Sup D W" "f (Sup D W)"])
apply (frule_tac x = x in bspec, assumption,
       thin_tac "\<forall>x\<in>insert (Sup D W) W. a \<preceq> x",
       simp)
apply (rule ballI)          
apply (cut_tac a = x in insert_iff[of _ "f (Sup D W)" "insert (Sup D W) W"],
        frule_tac P = "x \<in> insert (f (Sup D W)) (insert (Sup D W) W)" and 
         Q = "x = (f (Sup D W)) \<or> x \<in> (insert (Sup D W) W)" in eq_prop, 
                             assumption+,
        thin_tac "x \<in> insert (f (Sup D W)) (insert (Sup D W) W)",  
        thin_tac "(x \<in> insert (f (Sup D W)) (insert (Sup D W) W)) =
         (x = f (Sup D W) \<or> x \<in> insert (Sup D W) W)",
        erule disjE)
apply (frule not_sym, thin_tac "Sup D W \<noteq> f (Sup D W)",
       frule BNTr7_15[of "f" "a" "W"], assumption+,
       simp del:insert_iff insert_subset) 
apply (subst BNTr7_16[of "f" "a" "W"], assumption+, simp,
       frule S_inductive_sup_bound[of "W"], assumption+)
apply (subst BNTr7_11[of "f" "a" "f (Sup D W)" 
                         "insert (Sup D W) W"], assumption+,
       rule ballI,
       thin_tac "x \<in> insert (Sup D W) W", simp only:insert_iff,
       erule disjE,
       frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
       simp add:le_antisym,
       frule_tac x = xa in bspec, assumption+,
       thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
       frule_tac x = "Sup D W" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
       frule mem_WWa_sub_carrier[of "W"],
       frule_tac c = xa in subsetD[of "W" "carrier D"], assumption+,
       rule_tac a = xa in le_trans[of _ "Sup D W" "f (Sup D W)"],
       assumption+)
apply (case_tac "ExPre (Iod D (insert (Sup D W) W)) x",
       simp del:insert_iff insert_subset,
       subst BNTr7_12[of "f" "a" "f (Sup D W)" "insert (Sup D W) W"],
                assumption+,
       rule ballI, thin_tac "x \<in> insert (Sup D W) W",
              simp only:insert_iff, erule disjE,
         frule_tac x = "Sup D W" in bspec, assumption,
         thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
         simp add:le_antisym,
         frule_tac x = xa in bspec, assumption+,
              thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
         frule_tac x = "Sup D W" in bspec, assumption,
              thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
         frule mem_WWa_sub_carrier[of "W"],
         frule_tac c = xa in subsetD[of "W" "carrier D"], assumption+,
         rule_tac a = xa in le_trans[of _ "Sup D W" "f (Sup D W)"],
               assumption+)
       apply (frule mem_WWa_then[of "insert (Sup D W) W" "f" "a"],
              (erule conjE)+,
              thin_tac "\<forall>x\<in>insert (Sup D W) W. a \<preceq> x",
              frule_tac x = x in bspec, assumption,
              thin_tac "\<forall>x\<in>insert (Sup D W) W.
            if ExPre (Iod D (insert (Sup D W) W)) x
            then f (Pre (Iod D (insert (Sup D W) W)) x) = x
            else if a \<noteq> x
                 then Sup D (segment (Iod D (insert (Sup D W) W)) x) = x
                 else a = a", simp)
       apply (simp del:insert_iff insert_subset, rule impI)
  apply (subst BNTr7_13[of "f" "a" "f (Sup D W)" "insert (Sup D W) W"],
               assumption+,
         rule ballI, thin_tac "x \<in> insert (Sup D W) W",
              simp only:insert_iff,
         erule disjE,
         frule_tac x = "Sup D W" in bspec, assumption,
              thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
         simp add:le_antisym,
         frule_tac x = xa in bspec, assumption+,
              thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W",
         frule_tac x = "Sup D W" in bspec, assumption,
              thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x",
              frule mem_WWa_sub_carrier[of "W"],
              frule_tac c = xa in subsetD[of "W" "carrier D"], assumption+,
              rule_tac a = xa in le_trans[of _ "Sup D W" "f (Sup D W)"],
               assumption+)
       apply (frule mem_WWa_then[of "insert (Sup D W) W" "f" "a"],
              (erule conjE)+,
              thin_tac "\<forall>x\<in>insert (Sup D W) W. a \<preceq> x",
             frule_tac x = x in bspec, assumption,
              thin_tac "\<forall>x\<in>insert (Sup D W) W.
            if ExPre (Iod D (insert (Sup D W) W)) x
            then f (Pre (Iod D (insert (Sup D W) W)) x) = x
            else if a \<noteq> x
                 then Sup D (segment (Iod D (insert (Sup D W) W)) x) = x
                 else a = a", simp) 
done

lemma (in Order) BNTr8:"\<lbrakk>f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; 
          \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow>  \<Union> (WWa D f a) \<in> (WWa D f a)"
apply (cut_tac Union_WWa_sub_carrier[of "f" "a"])
apply (rule mem_of_WWa[of "\<Union>(WWa D f a)" "a" "f"], simp)
 apply (simp add:Worder_def Torder_def)
 apply (simp add:Iod_Order[of "\<Union>(WWa D f a)"])
 apply (rule conjI)
 apply (simp add:Torder_axioms_def)
 apply ((rule allI, rule impI)+, simp add:Iod_carrier,
         (erule bexE)+) 
 apply (rename_tac b c X1 X2)
 apply (frule_tac ?W1.0 = X1 and ?W2.0 = X2 in BNTr7[of "f" "a"],
           assumption+)
 apply (erule disjE)
 apply ((frule_tac c = b and A = X1 and B = X2 in subsetD, assumption+),
        (frule_tac W = X2 in mem_wwa_Worder[of _ "f" "a"]),
        (simp add:Worder_def Torder_def, (erule conjE)+,
         simp add:Torder_axioms_def),

       (frule_tac W = X1 in  mem_WWa_sub_carrier[of _ "f" "a"],
        frule_tac W = X2 in  mem_WWa_sub_carrier[of _ "f" "a"],
        simp add:Iod_carrier),
       (frule_tac a = b in forall_spec, assumption,
        thin_tac "\<forall>a. a \<in> X2 \<longrightarrow> (\<forall>b. b \<in> X2 \<longrightarrow>
                                a \<preceq>\<^bsub>Iod D X2\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X2\<^esub> a)",
        frule_tac a = c in forall_spec, assumption,
        thin_tac "\<forall>ba. ba \<in> X2 \<longrightarrow> b \<preceq>\<^bsub>Iod D X2\<^esub> ba \<or> ba \<preceq>\<^bsub>Iod D X2\<^esub> b",
        frule_tac X = X1 and A = b in UnionI[of _ "WWa D f a"], assumption+,
        frule_tac X = X2 and A = c in UnionI[of _ "WWa D f a"], assumption+,
        simp add:Iod_le)) 
 apply (frule_tac c = c and A = X2 and B = X1 in subsetD, assumption+,
        frule_tac W = X1 in mem_wwa_Worder[of _ "f" "a"],
        (simp add:Worder_def Torder_def, (erule conjE)+,
         simp add:Torder_axioms_def),

        (frule_tac W = X2 in  mem_WWa_sub_carrier[of _ "f" "a"],
         frule_tac W = X1 in  mem_WWa_sub_carrier[of _ "f" "a"],
         simp add:Iod_carrier,
         frule_tac a = b in forall_spec, assumption),
        thin_tac "\<forall>a. a \<in> X1 \<longrightarrow> (\<forall>b. b \<in> X1 \<longrightarrow>
                                a \<preceq>\<^bsub>Iod D X1\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X1\<^esub> a)",
        (frule_tac a = c in forall_spec, assumption,
         thin_tac "\<forall>ba. ba \<in> X1 \<longrightarrow> b \<preceq>\<^bsub>Iod D X1\<^esub> ba \<or> ba \<preceq>\<^bsub>Iod D X1\<^esub> b",
         frule_tac X = X1 and A = b in UnionI[of _ "WWa D f a"], assumption+,
         frule_tac X = X1 and A = c in UnionI[of _ "WWa D f a"], assumption+),
        simp add:Iod_le)

apply (subst Worder_axioms_def)
 apply (rule allI, rule impI, erule conjE)
 apply (frule_tac A = X in nonempty_ex, erule exE)
 apply (simp only:Iod_carrier,
        frule_tac c = x and A = X and B = "\<Union>(WWa D f a)" in subsetD,
        assumption, simp, erule bexE)
 apply (rename_tac X x W)
 apply (frule_tac W = W in mem_wwa_Worder[of _ "f" "a"],
        simp add:Worder_def Torder_def, erule conjE,
        simp add:Worder_axioms_def, erule conjE)
 apply (frule_tac a = "X \<inter> W" in forall_spec,
        thin_tac "\<forall>X. X \<subseteq> carrier (Iod D W) \<and> X \<noteq> {} \<longrightarrow>
            (\<exists>x. minimum_elem (Iod D W) X x)",
        frule_tac W = W in mem_WWa_sub_carrier[of _ "f" "a"],
        simp only:Iod_carrier, simp add:Int_lower2, blast,
        thin_tac "\<forall>X. X \<subseteq> carrier (Iod D W) \<and> X \<noteq> {} \<longrightarrow>
            (\<exists>x. minimum_elem (Iod D W) X x)", erule exE)
 apply (frule_tac W = W in mem_WWa_sub_carrier)
 apply (frule_tac D = "Iod D W" and X = "X \<inter> W" and a = xa in 
                      Order.minimum_elem_mem)
 apply (simp add:Iod_carrier)
 apply simp
apply (rule contrapos_pp, (simp del:Union_iff)+, erule conjE)
 apply (simp add:minimum_elem_def)
 apply (frule_tac a = xa in forall_spec, assumption+,
        thin_tac "\<forall>x. x \<in> X \<longrightarrow> (\<exists>xa\<in>X. \<not> x \<preceq>\<^bsub>Iod D (\<Union>(WWa D f a))\<^esub> xa)",
        erule bexE)
 apply (frule_tac c = xb and A = X and B = "\<Union>(WWa D f a)" in subsetD,
                 assumption+) 
apply (cut_tac A = xb and C = "WWa D f a" in Union_iff, simp del:Union_iff,
       erule bexE, rename_tac X x W xa xb W',
       frule_tac ?W1.0 = W and ?W2.0 = W' in BNTr7[of "f" "a"], assumption+)
 apply (case_tac "W' \<subseteq> W",
        frule_tac c = xb and A = W' and B = W in subsetD, assumption+,
        rotate_tac 4,
        frule_tac x = xb in bspec, simp,
        thin_tac "\<forall>x\<in>X \<inter> W. xa \<preceq>\<^bsub>Iod D W\<^esub> x")
 apply (frule Iod_Order[of "\<Union>(WWa D f a)"], 
        frule_tac X = W and A = xa in UnionI[of _ "WWa D f a"], assumption+,
        simp del:Union_iff add:Iod_le)
 apply (simp del:Union_iff)
 apply (frule_tac c = xa and A = W and B = W' in subsetD, assumption+,
        frule_tac X = W' and A = xa in UnionI[of _ "WWa D f a"], assumption+,
        frule_tac X = W' and A = xb in UnionI[of _ "WWa D f a"], assumption+)
 apply (simp only:Iod_le)
 apply (frule_tac W = W' in mem_wwa_Worder,
        frule_tac D = "Iod D W'" in Worder.Torder,
        frule_tac D = "Iod D W'" in Worder.Order)
 apply (frule_tac W = W' in mem_WWa_sub_carrier,
        frule_tac T1 = W' and a1 = xa and b1 = xb in Iod_le[THEN sym],
        assumption+, simp del:Union_iff)
 apply (frule_tac D = "Iod D W'" and a = xa and b = xb in Torder.not_le_less)
        apply (simp add:Iod_carrier) apply (simp add:Iod_carrier)
 apply (simp del:Union_iff add:Iod_less, thin_tac "\<not> xa \<preceq> xb", 
        thin_tac "\<not> xa \<preceq>\<^bsub>Iod D W'\<^esub> xb")
 apply (frule Iod_Order[of "\<Union>(WWa D f a)"])
 apply (frule_tac a1 = xb and b1 = xa in Iod_less[THEN sym, of "\<Union> (WWa D f a)"],
        assumption+, simp del:Union_iff,
        frule_tac x = xa and xa = xb and W = W in BNTr7_1[of "f" "a"], 
                        assumption+,
        frule_tac a1 = xb and b1 = xa and T1 = W in Iod_less[THEN sym],
           assumption+, simp del:Union_iff,
        frule_tac W = W in mem_wwa_Worder,
          frule_tac D = "Iod D W" in Worder.Torder)
   apply (frule_tac D1 = "Iod D W" and a1 = xa and b1 = xb in 
            Torder.not_le_less[THEN sym],
          simp add:Iod_carrier, simp add:Iod_carrier, simp del:Union_iff)
apply (rule BNTr7_6, assumption+)

apply (rule ballI) 
 apply (cut_tac A = x in Union_iff[of _ "WWa D f a"], simp del:Union_iff)
 apply (erule bexE, rename_tac x W)
 apply (simp add:WWa_def Wa_def[of "D" _ "f" "a"])

apply (rule ballI)
apply (case_tac "ExPre (Iod D (\<Union>(WWa D f a))) x", simp,
       erule bexE, rename_tac x W,
       frule_tac X = W and A = x in UnionI[of _ "WWa D f a"], assumption+,
       frule_tac x = x in BNTr7_2[of "f" "a"], assumption+,
       frule_tac x = W in bspec, assumption,
         thin_tac "\<forall>W\<in>WWa D f a. x \<in> W \<longrightarrow> ExPre (Iod D W) x",
         simp del:Union_iff)
  apply (frule_tac x = x in BNTr7_3[of "f" "a"], assumption+,
         frule_tac x = W in bspec, assumption,
         thin_tac "\<forall>W\<in>WWa D f a.
              x \<in> W \<longrightarrow> Pre (Iod D (\<Union>(WWa D f a))) x = Pre (Iod D W) x",
         simp del:Union_iff)
  apply (simp add:WWa_def Wa_def)

apply (simp del:Union_iff, rule impI) 
 apply (cut_tac A = x in Union_iff[of _ "WWa D f a"], simp del:Union_iff,
        erule bexE, rename_tac x W,
        frule_tac x = x and W = W in  BNTr7_5[of "f" "a" _], assumption+,
        simp)
 apply (frule_tac x = x and W = W in BNTr7_4[of "f" "a"], assumption+,
        simp del:Union_iff,
        thin_tac "\<Union>(WWa D f a) \<subseteq> carrier D",
        thin_tac "\<exists>X\<in>WWa D f a. x \<in> X",
        thin_tac "segment (Iod D (\<Union>(WWa D f a))) x = segment (Iod D W) x",
        thin_tac "\<not> ExPre (Iod D (\<Union>(WWa D f a))) x")
 apply (simp add:WWa_def Wa_def)
done

(*
lemma (in Order) BNTr9:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
           a \<in> carrier D;  \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow> 
            insert (Sup D (\<Union>(WWa D f a))) (\<Union>(WWa D f a)) \<in> WWa D f a"
apply (frule BNTr8[of "f" "a"], assumption+,
       rule BNTr7_14[of "f" "a" "\<Union>(WWa D f a)"], assumption+)
done

lemma (in Order) S_inductive_postSup_outside:" \<lbrakk>S_inductive_set D; 
       Chain D X; b \<in> carrier D; Sup D X \<prec> b\<rbrakk> \<Longrightarrow> b \<notin> X"
apply (frule S_inductive_sup_mem[of "X"], assumption+)
apply (rule contrapos_pp, simp+)
apply (frule S_inductive_sup_bound[of "X"], assumption,
       frule_tac a = b in bspec, assumption,
       thin_tac "\<forall>x\<in>X. x \<preceq> Sup D X",
       frule less_imp_le[of "Sup D X" "b"], assumption+)
apply (frule le_antisym[of "Sup D X" "b"], assumption+, simp add:oless_def)
done

lemma (in Order) S_inductive_adjunct_postSup_mem_WWa:"\<lbrakk>S_inductive_set D;
      \<forall>x\<in>carrier D. x \<preceq> (f x); W \<in> WWa D f a; b \<in> carrier D; (Sup D W) \<prec> b\<rbrakk>
       \<Longrightarrow>  insert b (insert (Sup D W) W) \<in> WWa D f a"
apply (frule mem_WWa_sub_carrier[of "W"],
       frule mem_WWa_Chain[of "W"],
       frule mem_wwa_Worder[of "W"],
       frule S_inductive_sup_mem[of "W"], assumption+)
apply (rule mem_of_WWa[of "insert b (insert (Sup D W) W)" "a" "f"],
       rule insert_sub[of "insert (Sup D W) W" "carrier D" "b"],
       rule insert_sub[of "W" "carrier D" "Sup D W"], assumption+) 
apply (frule S_inductive_sup_bound[of "W"], assumption+,
       frule insert_sub[of "W" "carrier D" "Sup D W"], assumption+)
apply (frule well_ord_adjunction[of "W" "Sup D W"], assumption+)
apply (frule well_ord_adjunction[of "insert (Sup D W) W" "b"], assumption+)
   apply (rule ballI, simp, erule disjE, simp add:less_imp_le,
          frule_tac a = x in bspec, assumption,
          thin_tac "\<forall>x\<in>W. x \<preceq> Sup D W")
   apply (frule_tac c = x in subsetD[of "W" "carrier D"], assumption+,
          frule less_imp_le[of "Sup D W" "b"], assumption+,
          frule_tac a = x in le_trans[of _ "Sup D W" "b"], assumption+,
          simp add:Un_commute[of "W" "{Sup D W}"],
          simp add:Un_commute[of "insert (Sup D W) W" "{b}"])
 apply (cut_tac subset_insertI[of "W" "Sup D W"],
        cut_tac subset_insertI[of "insert (Sup D W) W" "b"],
        frule mem_WWa_inc_a[of "W"], 
        frule subsetD[of "W" "insert (Sup D W) W" "a"], assumption+,
        frule subsetD[of "insert (Sup D W) W" "insert b (insert (Sup D W) W)" 
                       "a"], assumption+)
 apply (rule ballI) apply simp
 apply (erule disjE, simp,
        frule less_imp_le[of "Sup D W" "b"], assumption+,
        frule S_inductive_sup_bound[of "W"], assumption,
        frule mem_WWa_inc_a[of "W"], 
        frule_tac a = a in bspec, assumption,
        frule subsetD[of "W" "carrier D" "a"], assumption+,
        rule le_trans[of "a" "Sup D W" "b"], assumption+)
 apply (erule disjE, simp,
        frule mem_WWa_inc_a[of "W"], 
        frule S_inductive_sup_bound[of "W"], assumption,
        simp, simp  add:WWa_def Wa_def)
 apply (rule ballI)
 apply (simp only:insert_iff)
 apply (erule disjE)*)

lemma (in Order) BNTr10:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
   a \<in> carrier D;  \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow>
                   (Sup D (\<Union>(WWa D f a))) \<in> (\<Union>(WWa D f a))"
apply (frule_tac f = f and a = a in BNTr8, assumption+,
       frule BNTr7_14[of "f" "a" "\<Union>(WWa D f a)"], assumption+,
       frule mem_family_sub_Un[of "insert (Sup D (\<Union>(WWa D f a))) (\<Union>(WWa D f a))"
          "WWa D f a"],
       cut_tac insertI1[of "Sup D (\<Union>(WWa D f a))" "\<Union>(WWa D f a)"])
apply (simp add:subsetD)
done         

lemma (in Order) BNTr11:"\<lbrakk>S_inductive_set D; f \<in> carrier D \<rightarrow> carrier D; 
                 a \<in> carrier D;  \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow> 
                   f (Sup D (\<Union>(WWa D f a))) = (Sup D (\<Union>(WWa D f a)))"
apply (frule_tac f = f and a = a in BNTr8, assumption+,
       frule mem_WWa_Chain[of "\<Union>(WWa D f a)"],
       frule BNTr10[of "f" "a"], assumption+,
       frule S_inductive_sup_mem[of "\<Union>(WWa D f a)"], assumption)
apply (frule BNTr7_17[of "f" "a" "\<Union>(WWa D f a)"], assumption+) 
apply (cut_tac insertI1[of "f (Sup D (\<Union>(WWa D f a)) )" "insert (Sup D (\<Union>(WWa D f a))) (\<Union>(WWa D f a))"],
       frule mem_family_sub_Un[of "insert (f (Sup D (\<Union>(WWa D f a))))
      (insert (Sup D (\<Union>(WWa D f a))) (\<Union>(WWa D f a)))" "(WWa D f a)"])
apply (frule subsetD[of "insert (f (Sup D (\<Union>(WWa D f a)))) 
        (insert (Sup D (\<Union>(WWa D f a))) (\<Union>(WWa D f a)))" "\<Union>(WWa D f a)" "f (Sup D (\<Union>(WWa D f a)))"],
         assumption+)
apply (frule S_inductive_sup_bound[of "\<Union>(WWa D f a)"], assumption) 
apply (frule_tac x = "f (Sup D (\<Union>(WWa D f a)))" in bspec,
       assumption,
       thin_tac "\<forall>x\<in>\<Union>(WWa D f a). x \<preceq> Sup D (\<Union>(WWa D f a))")
apply (frule_tac x = "Sup D (\<Union>(WWa D f a))" in bspec, assumption,
       thin_tac "\<forall>x\<in>carrier D. x \<preceq> f x")
apply (frule funcset_mem[of "f" "carrier D" "carrier D" "Sup D (\<Union>(WWa D f a))"],
       assumption+,
       rule le_antisym[of "f (Sup D (\<Union>(WWa D f a)))" "Sup D (\<Union>(WWa D f a))"], 
        assumption+)
done

lemma (in Order) Bourbaki_Nakayama:"\<lbrakk>S_inductive_set D; 
      f \<in> carrier D \<rightarrow> carrier D; a \<in> carrier D; \<forall>x\<in>carrier D. x \<preceq> (f x)\<rbrakk> \<Longrightarrow>
      \<exists>x0\<in>carrier D. f x0 = x0"
apply (frule BNTr8[of "f" "a"], assumption+,
       frule mem_WWa_Chain[of "\<Union>(WWa D f a)" "f" "a"],
       frule S_inductive_sup_mem[of "\<Union>(WWa D f a)"], assumption+,
       frule BNTr11[of "f" "a"], assumption+)
apply blast
done

definition
  maxl_fun :: " _  \<Rightarrow> 'a \<Rightarrow> 'a" where
  "maxl_fun D = (\<lambda>x\<in>carrier D. if \<exists>y. y\<in>(upper_bounds D {x}) \<and> y \<noteq> x then
    SOME z. z \<in> (upper_bounds D {x}) \<and> z \<noteq> x else x)"

lemma (in Order) maxl_funTr:"\<lbrakk>x \<in> carrier D; 
      \<exists>y. y \<in> upper_bounds D {x} \<and> y \<noteq> x\<rbrakk> \<Longrightarrow> 
      (SOME z. z \<in> upper_bounds D {x} \<and> z \<noteq> x) \<in> carrier D"
apply (rule someI2_ex, assumption+,
       simp add:upper_bounds_def upper_bound_def)
done

lemma (in Order) maxl_fun_func:"maxl_fun D \<in> carrier D \<rightarrow> carrier D"
by (simp add:maxl_fun_def maxl_funTr)

lemma (in Order) maxl_fun_gt:"\<lbrakk>x \<in> carrier D; 
      \<exists>y\<in> carrier D.  x \<preceq> y \<and> x \<noteq> y \<rbrakk> \<Longrightarrow> 
          x \<preceq> (maxl_fun D x) \<and> (maxl_fun D x) \<noteq> x"
apply (simp add:maxl_fun_def upper_bounds_def upper_bound_def,
       rule conjI, rule impI)
apply (rule someI2_ex, assumption+, simp,
       erule bexE, blast)
done


lemma (in Order) maxl_fun_maxl:"\<lbrakk>x \<in> carrier D; maxl_fun D x = x \<rbrakk>
      \<Longrightarrow> maximal x"
apply (rule contrapos_pp, simp+, simp add:maximal_element_def)
apply (frule maxl_fun_gt[of "x"], assumption, erule conjE, simp)
done

lemma (in Order) maxl_fun_asc:"\<forall>x\<in>carrier D. x \<preceq> (maxl_fun D x)"
apply (rule ballI)
apply (simp add:maxl_fun_def, rule conjI, rule impI)  
 apply (rule someI2_ex, assumption, simp add:upper_bounds_def upper_bound_def,
        rule impI, rule le_refl, assumption)
done

lemma (in Order) S_inductive_maxl:"\<lbrakk>S_inductive_set D; carrier D \<noteq> {}\<rbrakk> \<Longrightarrow> 
          \<exists>m. maximal m"
apply (frule nonempty_ex [of "carrier D"],
       erule exE, rename_tac a)
 apply (cut_tac maxl_fun_asc, cut_tac maxl_fun_func,
        frule_tac a = a in Bourbaki_Nakayama[of "maxl_fun D" _], assumption+)
 apply (erule bexE,
        frule_tac x = x0 in maxl_fun_maxl, assumption+)
 apply blast
done

lemma (in Order) maximal_mem:"maximal m \<Longrightarrow> m \<in> carrier D"
by (simp add:maximal_element_def)

definition
  Chains :: " _  \<Rightarrow> ('a set) set" where
  "Chains D == {C. Chain D C}"

definition
  family_Torder::" _  \<Rightarrow> ('a set) Order"
    ("(fTo _)" [999]1000) where
  "fTo D = \<lparr>carrier = Chains D , rel = {Z. Z \<in> (Chains D) \<times> (Chains D) \<and> (fst Z) \<subseteq> (snd Z)}\<rparr>"

lemma (in Order) Chain_mem_fTo:"Chain D C \<Longrightarrow> C \<in> carrier (fTo D)"
by (simp add:family_Torder_def Chains_def)

lemma (in Order) fTOrder:"Order (fTo D)"
apply (subst Order_def)
 apply (simp add:family_Torder_def)
 apply auto
done

lemma (in Order) fTo_Order_sub:"\<lbrakk>A \<in> carrier (fTo D); B \<in> carrier (fTo D)\<rbrakk>
         \<Longrightarrow> (A \<preceq>\<^bsub>(fTo D)\<^esub> B) = (A \<subseteq> B)"
by (subst ole_def, simp add:family_Torder_def)


lemma (in Order) mem_fTo_Chain:"X \<in> carrier (fTo D) \<Longrightarrow> Chain D X"
by (simp add:family_Torder_def Chains_def)

lemma (in Order) mem_fTo_sub_carrier:"X \<in> carrier (fTo D) \<Longrightarrow> X \<subseteq> carrier D"
by (frule mem_fTo_Chain[of "X"], simp add:Chain_sub)

lemma (in Order) Un_fTo_Chain:"Chain (fTo D) CC \<Longrightarrow> Chain D (\<Union> CC)" 
apply (cut_tac fTOrder,
       frule Order.Chain_sub[of "fTo D" "CC"], assumption+,
       cut_tac family_subset_Un_sub[of "CC" "carrier D"],
       subst Chain_def, simp, simp add:Torder_def, simp add:Iod_Order,
       simp add:Torder_axioms_def)
apply ((rule allI, rule impI)+, simp add:Iod_carrier)
apply ((erule bexE)+,
        frule_tac A = X in mem_family_sub_Un[of _ "CC"],
        frule_tac A = Xa in mem_family_sub_Un[of _ "CC"],
        frule_tac c = a and A = X in subsetD[of _ "\<Union>CC"], assumption+,
        frule_tac c = b and A = Xa in subsetD[of _ "\<Union>CC"], assumption+,
        simp only:Iod_le,
        frule_tac c = X in subsetD[of "CC" "carrier fTo D"], assumption+,
        frule_tac c = Xa in subsetD[of "CC" "carrier fTo D"], assumption+)
 apply (simp add:Chain_def Torder_def Torder_axioms_def,
        thin_tac "\<exists>X\<in>CC. a \<in> X", thin_tac "\<exists>X\<in>CC. b \<in> X",
        (erule conjE)+,
        frule_tac a = X in forall_spec,
        simp only:Order.Iod_carrier[of "fTo D" "CC"],
        thin_tac "\<forall>a. a \<in> carrier (Iod (fTo D) CC) \<longrightarrow>
            (\<forall>b. b \<in> carrier (Iod (fTo D) CC) \<longrightarrow>
                 a \<preceq>\<^bsub>Iod (fTo D) CC\<^esub> b \<or> b \<preceq>\<^bsub>Iod (fTo D) CC\<^esub> a)",
        frule_tac a = Xa in forall_spec,
        simp only:Order.Iod_carrier[of "fTo D" "CC"],
        thin_tac "\<forall>b. b \<in> carrier (Iod (fTo D) CC) \<longrightarrow>
            X \<preceq>\<^bsub>Iod (fTo D) CC\<^esub> b \<or> b \<preceq>\<^bsub>Iod (fTo D) CC\<^esub> X")
   apply (simp add:Order.Iod_le) apply (simp add:fTo_Order_sub)
   apply (frule_tac X = X in mem_fTo_Chain,
          frule_tac X = Xa in mem_fTo_Chain,
          frule_tac X = X in Chain_Torder,
          frule_tac X = Xa in Chain_Torder,
          frule_tac X = X in Chain_sub,
          frule_tac X = Xa in Chain_sub) 
  apply (simp add:Torder_def Torder_axioms_def, (erule conjE)+, 
         simp only:Iod_carrier)
  apply (erule disjE,
      frule_tac c = a and A = X and B = Xa in subsetD, assumption+,
      thin_tac "\<forall>a. a \<in> X \<longrightarrow> (\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> a)",
      frule_tac a = a in forall_spec,
      thin_tac "\<forall>a. a \<in> Xa \<longrightarrow> (\<forall>b. b \<in> Xa \<longrightarrow> a \<preceq>\<^bsub>Iod D Xa\<^esub> b \<or> b \<preceq>\<^bsub>Iod D Xa\<^esub> a)",
      assumption,
      thin_tac "\<forall>a. a \<in> Xa \<longrightarrow> (\<forall>b. b \<in> Xa \<longrightarrow> a \<preceq>\<^bsub>Iod D Xa\<^esub> b \<or> b \<preceq>\<^bsub>Iod D Xa\<^esub> a)",
      frule_tac a = b in forall_spec, assumption,
      thin_tac "\<forall>b. b \<in> Xa \<longrightarrow> a \<preceq>\<^bsub>Iod D Xa\<^esub> b \<or> b \<preceq>\<^bsub>Iod D Xa\<^esub> a",
      simp add:Iod_le)
   apply (
      frule_tac c = b and A = Xa and B = X in subsetD, assumption+,
      thin_tac "\<forall>a. a \<in> Xa \<longrightarrow> (\<forall>b. b \<in> Xa \<longrightarrow> a \<preceq>\<^bsub>Iod D Xa\<^esub> b \<or> b \<preceq>\<^bsub>Iod D Xa\<^esub> a)",
      frule_tac a = a in forall_spec,
      thin_tac "\<forall>a. a \<in> X \<longrightarrow> (\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> a)",
      assumption,
      thin_tac "\<forall>a. a \<in> X \<longrightarrow> (\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> a)",
      frule_tac a = b in forall_spec, assumption,
      thin_tac "\<forall>b. b \<in> X \<longrightarrow> a \<preceq>\<^bsub>Iod D X\<^esub> b \<or> b \<preceq>\<^bsub>Iod D X\<^esub> a",
      simp add:Iod_le) 
 
 apply (rule ballI,
        frule_tac c = A in subsetD[of "CC" "carrier (fTo D)"], assumption+,
        rule mem_fTo_sub_carrier, assumption+)
done  

lemma (in Order) Un_fTo_Chain_mem_fTo:"Chain (fTo D) CC \<Longrightarrow>
                  (\<Union> CC) \<in> carrier (fTo D)" 
apply (frule Un_fTo_Chain[of "CC"], thin_tac "Chain (fTo D) CC")
apply (simp add:family_Torder_def Chains_def)
done

lemma (in Order) Un_upper_bound:"Chain (fTo D) C \<Longrightarrow>
                  \<Union>C \<in> upper_bounds (fTo D) C"
apply (simp add:upper_bounds_def upper_bound_def,
       simp add:Un_fTo_Chain_mem_fTo)
apply (rule ballI,
       simp add:ole_def,
       subst family_Torder_def, simp)

apply (cut_tac fTOrder,
       frule Order.Chain_sub[of "fTo D" "C"], assumption,
       frule_tac c = s in subsetD[of "C" "carrier (fTo D)"], assumption+,
       cut_tac Un_fTo_Chain_mem_fTo[of "C"],
       simp add:mem_fTo_Chain Chains_def,
       rule_tac A = s in mem_family_sub_Un[of _ "C"], assumption)
apply assumption
done

lemma (in Order) fTo_conditional_inc_C:"C \<in> carrier (fTo D) \<Longrightarrow> 
        C \<in> carrier (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S})"
apply (cut_tac fTOrder,
       cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"])
apply (simp add:Order.Iod_carrier)
done

lemma (in Order) fTo_conditional_Un_Chain_mem1:" \<lbrakk>C \<in> carrier (fTo D); 
     Chain (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca; Ca \<noteq> {}\<rbrakk> \<Longrightarrow>
      \<Union>Ca \<in> upper_bounds (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S}) Ca"
 
apply (cut_tac fTOrder,
       cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"])

  apply (simp add:upper_bounds_def upper_bound_def)
  apply (subgoal_tac "\<Union>Ca \<in>carrier (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})")
   apply simp
   apply (rule ballI)
   apply (force simp add: Chain_def Order.Iod_carrier Order.Iod_le Union_upper fTo_Order_sub subset_eq)  
  apply (simp add:Order.Iod_carrier[of "fTo D"])
  apply (rule conjI)
   apply (rule Un_fTo_Chain_mem_fTo[of "Ca"])
   apply (force simp add: Chain_def Order.Iod_carrier Order.Iod_sub_sub)
  apply (simp add:Chain_def, erule conjE)
  apply (rule sub_Union[of "Ca" "C"])
  using Order.Iod_carrier by fastforce

lemma (in Order) fTo_conditional_min1:" \<lbrakk>C \<in> carrier (fTo D); 
     Chain (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca; Ca \<noteq> {}\<rbrakk> \<Longrightarrow>
      minimum_elem (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S})
        (upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca) (\<Union>Ca)"
apply (frule fTo_conditional_Un_Chain_mem1[of "C" "Ca"], assumption+,
       simp add:minimum_elem_def)
apply (rule ballI)
 apply (simp add:upper_bounds_def upper_bound_def, (erule conjE)+,
        cut_tac fTOrder,
        cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"])
 apply (simp only:Order.Iod_carrier,
        simp only:Order.Iod_le[of "fTo D"])
 apply (frule_tac c = "\<Union>Ca" in subsetD[of "{S \<in> carrier fTo D. C \<subseteq> S}"
         "carrier (fTo D)"], assumption+,
        frule_tac c = x in subsetD[of "{S \<in> carrier fTo D. C \<subseteq> S}"
         "carrier (fTo D)"], assumption+)
  apply (subst Order.fTo_Order_sub, rule Order_axioms, assumption, simp,
         rule_tac C = Ca and B = x in family_subset_Un_sub)
  apply (rule ballI)
  apply (thin_tac "\<forall>s\<in>Ca. s \<preceq>\<^bsub>Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}\<^esub> \<Union>Ca",
         frule_tac x = A in bspec, assumption,
         thin_tac "\<forall>s\<in>Ca. s \<preceq>\<^bsub>Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}\<^esub> x")
  apply (frule Order.Iod_Order[of "fTo D" "{S \<in> carrier fTo D. C \<subseteq> S}"],
                      assumption,
         frule Order.Chain_sub[of "Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}"
           "Ca"], assumption,
         simp only:Order.Iod_carrier[of "fTo D" "{S \<in> carrier fTo D. C \<subseteq> S}"])
  apply (frule_tac c = x in subsetD[of "{x \<in> carrier fTo D. C \<subseteq> x}"
                             "carrier (fTo D)"], simp,
         frule_tac c = A in subsetD[of "Ca" "{x \<in> carrier fTo D. C \<subseteq> x}"],
                              assumption+,
         frule_tac a = A and b = x in Order.Iod_le[of "fTo D" 
                   "{x \<in> carrier fTo D. C \<subseteq> x}"], assumption+)
    apply simp apply (simp add:fTo_Order_sub)
done
 
lemma (in Order) fTo_conditional_Un_Chain_mem2:" \<lbrakk>C \<in> carrier (fTo D); 
       Chain (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S}) Ca; Ca = {}\<rbrakk> \<Longrightarrow>
       C \<in> upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca"
apply (cut_tac fTOrder,
       cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"])
apply (simp add:upper_bounds_def upper_bound_def, simp add:Order.Iod_carrier)
done

lemma (in Order) fTo_conditional_min2:" \<lbrakk>C \<in> carrier (fTo D); 
     Chain (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca; Ca = {}\<rbrakk> \<Longrightarrow>
      minimum_elem (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S})
        (upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca) C"
apply (simp add:minimum_elem_def upper_bounds_def upper_bound_def)
apply (cut_tac fTOrder,
       cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"],
       simp add:Order.Iod_carrier)
  by (auto simp add: Order.Iod_le fTo_Order_sub)


lemma (in Order) fTo_S_inductive:"S_inductive_set (fTo D)"
apply (simp add:S_inductive_set_def,
       rule allI, rule impI)
apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def,
        frule_tac CC = C in Un_fTo_Chain_mem_fTo,
        frule_tac x = "\<Union>C" in bspec, assumption,
         thin_tac "\<forall>x\<in>carrier (fTo D).
            x \<in> upper_bounds (fTo D) C \<longrightarrow>
            (\<exists>xa\<in>upper_bounds (fTo D) C. \<not> x \<preceq>\<^bsub>(fTo D)\<^esub> xa)")
 apply (frule_tac C = C in Un_upper_bound, simp,
        erule bexE,
        thin_tac "\<Union>C \<in> upper_bounds (fTo D) C")
 apply (simp add:upper_bounds_def upper_bound_def,
        erule conjE)
 apply (cut_tac C = C and B = x in family_subset_Un_sub)
 apply (rule ballI)
 apply (frule_tac x = A in bspec, assumption,
        thin_tac "\<forall>s\<in>C. s \<preceq>\<^bsub>fTo D\<^esub> x",
        cut_tac fTOrder,
        frule_tac X = C in Order.Chain_sub[of "fTo D"], assumption+,
        frule_tac c = A and A = C in subsetD[of _ "carrier (fTo D)"],
                        assumption+,
        simp add:fTo_Order_sub)
 apply (simp add:fTo_Order_sub)
done

lemma (in Order) conditional_min_upper_bound:" \<lbrakk>C \<in> carrier (fTo D);
      Chain (Iod (fTo D) {S \<in> carrier fTo D. C \<subseteq> S}) Ca\<rbrakk> \<Longrightarrow> 
      \<exists>X. minimum_elem (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})
         (upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca) X"
apply (case_tac "Ca = {}",
        frule fTo_conditional_min2[of "C"], assumption+, blast,
        frule fTo_conditional_min1[of "C"], assumption+, blast)
done

lemma (in Order) Hausdorff_acTr:"C \<in> carrier (fTo D) \<Longrightarrow>
       S_inductive_set (Iod (fTo D) {S. S \<in> (carrier (fTo D)) \<and>  C \<subseteq> S})"
apply (simp add:S_inductive_set_def)
 apply (rule allI, rule impI)
 apply (frule_tac Ca = Ca in conditional_min_upper_bound[of "C"],
         assumption+)
 apply (erule exE, cut_tac fTOrder)
 apply (cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"])
 apply (frule Order.Iod_Order[of "fTo D" "{S \<in> carrier fTo D. C \<subseteq> S}"],
          assumption+)
 apply (frule_tac X = "upper_bounds (Iod (fTo D) 
                              {S \<in> carrier (fTo D). C \<subseteq> S}) Ca"
   and a = X in 
   Order.minimum_elem_mem[of "Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}"])
 apply (simp only:Order.Iod_carrier)
 apply (rule subsetI,
        thin_tac "minimum_elem (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})
         (upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca) X")
 apply (simp add:upper_bounds_def upper_bound_def, erule conjE)
 apply (simp add:Order.Iod_carrier) apply assumption 
 apply (subgoal_tac "X\<in>carrier (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) ")
 apply blast
 apply (frule_tac X = Ca in Order.Chain_sub[of "Iod (fTo D) 
        {S \<in> carrier (fTo D). C \<subseteq> S}"], assumption,
        frule_tac X = Ca in Order.upper_bounds_sub[of 
         "Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}"], assumption)
 apply (thin_tac "minimum_elem (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})
         (upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}) Ca) X")
 apply (rule_tac A = "upper_bounds (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})
        Ca" and B = "carrier (Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S})" and 
        c = X  in subsetD, assumption+)
done

lemma  satisfy_cond_mem_set:"\<lbrakk> x \<in> A; P x \<rbrakk> \<Longrightarrow> x \<in> {y \<in> A. P y}"
by blast

lemma (in Order) maximal_conditional_maximal:" \<lbrakk>C \<in> carrier (fTo D);
       maximal\<^bsub>Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}\<^esub> m\<rbrakk> \<Longrightarrow> maximal\<^bsub>(fTo D)\<^esub> m"
apply (unfold maximal_element_def, erule conjE)
apply (cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"],
       cut_tac fTOrder,
       frule Order.Iod_Order[of "fTo D" "{x \<in> carrier fTo D. C \<subseteq> x}"],
       assumption+,
       simp only:Order.Iod_carrier,
       frule subsetD[of "{S \<in> carrier fTo D. C \<subseteq> S}" 
              "carrier (fTo D)" "m"], assumption+, simp)
apply (rule ballI, rule impI) 
 apply (simp only:fTo_Order_sub,
        frule_tac a = b in forall_spec, simp,
        thin_tac "\<forall>b. b \<in> carrier (fTo D) \<and> C \<subseteq> b \<longrightarrow>
             m \<preceq>\<^bsub>Iod (fTo D) {S \<in> carrier (fTo D). C \<subseteq> S}\<^esub> b \<longrightarrow> m = b")
  by (simp add: Order.Iod_le fTo_Order_sub)

lemma (in Order) Hausdorff_ac:"C \<in> carrier (fTo D) \<Longrightarrow> 
                    \<exists>M\<in>carrier (fTo D). C \<subseteq> M \<and> maximal\<^bsub>(fTo D)\<^esub> M"
apply (frule_tac Hausdorff_acTr[of "C"],
       cut_tac conditional_subset[of "carrier (fTo D)" "(\<subseteq>) C"],
       cut_tac fTOrder,
       frule Order.Iod_Order[of "fTo D" "{x \<in> carrier fTo D. C \<subseteq> x}"],
       assumption+)
apply (frule Order.S_inductive_maxl[of "Iod (fTo D) 
              {S \<in> carrier (fTo D). C \<subseteq> S}"], assumption+,
       frule fTo_conditional_inc_C[of "C"], simp add:nonempty,
       erule exE,
       frule_tac m = m in Order.maximal_mem[of 
             "Iod (fTo D) {x \<in> carrier (fTo D). C \<subseteq> x}"], assumption+,
       simp add:Order.Iod_carrier, erule conjE,
       frule_tac m = m in maximal_conditional_maximal[of "C"], assumption+)
apply blast
done

(** g_Zorn_lemma is the Zorn's lemma in general ordered set **)
lemma (in Order) Zorn_lemmaTr:"\<lbrakk>Chain D C; M \<in> carrier fTo D; C \<subseteq> M;
           maximal\<^bsub>fTo D\<^esub> M; b \<in> carrier D; \<forall>s\<in>M. s \<preceq> b \<rbrakk> \<Longrightarrow>
            maximal b \<and> b \<in> upper_bounds D C"
apply (simp add:upper_bounds_def upper_bound_def)
apply (rule conjI)
prefer 2
 apply (rule ballI, simp add:subsetD,
        rule contrapos_pp, simp+, simp add:maximal_element_def,
        erule bexE, erule conjE)
 apply (frule_tac X = M in mem_fTo_Chain,
        frule_tac X = M and b = ba in adjunct_Chain, assumption+,
        rule ballI)
 apply (frule_tac x = x in bspec, assumption+,
        thin_tac "\<forall>s\<in>M. s \<preceq> b",
        frule_tac X = M in Chain_sub,
        frule_tac c = x in subsetD[of "M" "carrier D"], assumption+,
        rule_tac a = x and b = b and c = ba in le_trans, assumption+)
 apply (cut_tac B = M and a = ba in subset_insertI,
        cut_tac a = ba in insertI1[of _ "M"], 
        cut_tac C = "insert ba M" in Chain_mem_fTo, assumption)
 apply (frule_tac x = "insert ba M" in bspec, assumption,
        thin_tac "\<forall>b\<in>carrier fTo D. M \<preceq>\<^bsub>fTo D\<^esub> b \<longrightarrow> M = b",
        simp del:insert_iff insert_subset add:fTo_Order_sub)
 apply (frule_tac x = ba in bspec, assumption,
        thin_tac "\<forall>s\<in>M. s \<preceq> b")
 apply (frule_tac a = b and b = ba in le_antisym, assumption+, simp)
done

lemma (in Order) g_Zorn_lemma1:"\<lbrakk>inductive_set D; Chain D C\<rbrakk> \<Longrightarrow> \<exists>m. maximal m \<and> m \<in> upper_bounds D C"
apply (frule Chain_mem_fTo [of "C"],
       frule Hausdorff_ac[of "C"]) 
 apply (erule bexE, erule conjE)
 apply (frule_tac X = M in mem_fTo_Chain)
 apply (simp add:inductive_set_def)
 apply (frule_tac a = M in forall_spec, assumption,
        thin_tac "\<forall>C. Chain D C \<longrightarrow> (\<exists>b. ub C b)",
        erule exE, simp add:upper_bound_def, erule conjE)
 apply (frule_tac M = M and b = b in Zorn_lemmaTr[of "C"], assumption+)
 apply blast
done

lemma (in Order) g_Zorn_lemma2:"\<lbrakk>inductive_set D; a \<in> carrier D\<rbrakk> \<Longrightarrow> 
                 \<exists>m\<in>carrier D. maximal m \<and> a \<preceq> m" 
apply (frule BNTr1 [of "a"],
       frule singleton_sub[of "a" "carrier D"],
       frule_tac  X = "{a}" in Torder_Chain,
       simp add:Worder.Torder)
apply (frule_tac C = "{a}" in g_Zorn_lemma1, assumption+,
       erule exE, erule conjE,
       simp add:upper_bounds_def upper_bound_def)
apply blast
done

lemma (in Order) g_Zorn_lemma3:"inductive_set D \<Longrightarrow> \<exists>m\<in>carrier D. maximal m"
apply (cut_tac Iod_empty_Torder,
       cut_tac empty_subsetI[of "carrier D"],
       frule Torder_Chain[of "{}"], assumption+)
apply (frule_tac  C = "{}" in g_Zorn_lemma1, assumption+,
       simp add:upper_bounds_def upper_bound_def,
       blast)
done

chapter "Group Theory. Focused on Jordan Hoelder theorem"
    

section "Definition of a Group"

record 'a Group = "'a carrier" + 
  top      :: "['a, 'a ] \<Rightarrow> 'a" (infixl "\<cdot>\<index>" 70)
  iop      :: "'a  \<Rightarrow>  'a" ("\<rho>\<index> _" [81] 80)
  one     :: "'a"   ("\<one>\<index>") 

locale Group =
 fixes G (structure)
 assumes top_closed: "top G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G"
 and     tassoc : "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow>
         (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
 and     iop_closed:"iop G \<in> carrier G \<rightarrow> carrier G"
 and     l_i :"a \<in> carrier G \<Longrightarrow>  (\<rho> a) \<cdot> a = \<one>"
 and     unit_closed: "\<one> \<in> carrier G"
 and     l_unit:"a \<in> carrier G \<Longrightarrow> \<one> \<cdot> a = a"


lemma (in Group) mult_closed:"\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow>
           a \<cdot> b \<in> carrier G"
apply (cut_tac top_closed)
apply (frule funcset_mem[of "(\<cdot>)" "carrier G" "carrier G \<rightarrow> carrier G" "a"],
       assumption+,
       frule funcset_mem[of "(\<cdot>) a" "carrier G" "carrier G" "b"],
       assumption+ )
done
    
lemma (in Group) i_closed:"a \<in> carrier G \<Longrightarrow> (\<rho> a) \<in> carrier G" 
apply  (cut_tac iop_closed,
       frule funcset_mem[of "iop G" "carrier G" "carrier G" "a"])
apply assumption+
done

lemma (in Group) r_mult_eqn:"\<lbrakk>a \<in> carrier G; b \<in> carrier G;
       c \<in> carrier G; a = b\<rbrakk> \<Longrightarrow> a \<cdot> c = b \<cdot> c"
by simp

lemma (in Group) l_mult_eqn:"\<lbrakk>a \<in> carrier G; b \<in> carrier G;
       c \<in> carrier G; a = b\<rbrakk> \<Longrightarrow> c \<cdot> a = c \<cdot> b"
by simp

lemma (in Group) r_i:"a \<in> carrier G \<Longrightarrow>
                    a \<cdot> (\<rho> a) = \<one> "
apply (frule mult_closed[of "a" "\<rho> a"],
       simp add:i_closed,
       cut_tac l_unit[of "a"],
       cut_tac unit_closed,
       frule mult_closed[of "\<one>" "a"], assumption+,
       frule i_closed[of "a"],
       frule mult_closed[of "\<rho> a" "a"], assumption+)

 apply (frule r_mult_eqn[of "(\<rho> a) \<cdot> a" "\<one>" "\<rho> a"], assumption+,
        simp add:l_i,
        simp add:l_unit[of "\<rho> a"])

(* (i i a) from the left  *) 
 apply (frule i_closed[of "a"],
        frule i_closed[of "\<rho> a"],
        frule mult_closed[of "\<rho> a" "a"], assumption+,
        frule mult_closed[of "(\<rho> a) \<cdot> a" "\<rho> a"], assumption+,
        frule l_mult_eqn[of "(\<rho> a) \<cdot> a \<cdot> (\<rho> a)" "\<rho> a" "\<rho> (\<rho> a)"],
        assumption+) 
 apply (thin_tac "(\<rho> a) \<cdot> a \<cdot> (\<rho> a) = (\<rho> a)",
        simp add:l_i[of "\<rho> a"],
        simp add:tassoc[THEN sym, of "\<rho> (\<rho> a)" "(\<rho> a) \<cdot> a" "\<rho> a"],
        simp add:tassoc[THEN sym, of "\<rho> (\<rho> a)" "\<rho> a" "a"])
 apply (simp add:l_i[of "\<rho> a"])
apply assumption
done

lemma (in Group) r_unit:"a \<in> carrier G \<Longrightarrow> a \<cdot> \<one> = a"
apply (cut_tac unit_closed,
       frule i_closed[of "a"],
       frule mult_closed[of "a" "\<one>"], assumption+)
apply (cut_tac l_i[THEN sym, of "a"],
       simp,
       thin_tac "\<one> = \<rho> a \<cdot> a")
   
apply (simp add:tassoc[THEN sym] r_i l_unit)
apply assumption
done

lemma (in Group) l_i_unique:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; 
       b \<cdot> a = \<one> \<rbrakk> \<Longrightarrow> (\<rho> a) = b "
apply (cut_tac unit_closed,
       frule i_closed[of "a"],
       frule mult_closed[of "b" "a"], assumption+)
apply (frule r_mult_eqn[of "b \<cdot> a" "\<one>" "\<rho> a"], assumption+)
apply (thin_tac "b \<cdot> a = \<one>",
       simp add:tassoc[of "b" "a" "\<rho> a"] r_i)
apply (simp add:l_unit r_unit)
done

lemma (in Group) l_i_i:"a \<in> carrier G \<Longrightarrow> (\<rho> (\<rho> a)) \<cdot> (\<rho> a) = \<one>"
by (frule i_closed[of "a"],
       cut_tac l_i[of "\<rho> a"], assumption+) 

lemma (in Group) l_div_eqn:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; y \<in> carrier G;
        a \<cdot> x = a \<cdot> y \<rbrakk> \<Longrightarrow> x = y"
apply (frule mult_closed[of "a" "x"], assumption+,
       frule mult_closed[of "a" "y"], assumption+,
       frule i_closed[of "a"],
       frule l_mult_eqn[of "a \<cdot> x" "a \<cdot> y" "\<rho> a"], assumption+)
apply (thin_tac "a \<cdot> x = a \<cdot> y",
       simp add:tassoc[THEN sym])
apply (simp add:l_i l_unit)
done

lemma (in Group) r_div_eqn:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; y \<in> carrier G;
   x \<cdot> a = y \<cdot> a \<rbrakk> \<Longrightarrow> x = y "
apply (frule mult_closed[of "x" "a"], assumption+,
       frule mult_closed[of "y" "a"], assumption+,
       frule i_closed[of "a"],
       frule r_mult_eqn[of "x \<cdot> a" "y \<cdot> a" "\<rho> a"], assumption+)
 apply (thin_tac "x \<cdot> a =  y \<cdot> a",
        simp add:tassoc, simp add:r_i r_unit)
done

lemma (in Group) l_mult_eqn1:"\<lbrakk>a \<in> carrier G; x \<in> carrier G;  y \<in> carrier G;
        (\<rho> a) \<cdot> x = (\<rho> a) \<cdot> y\<rbrakk>  \<Longrightarrow> x = y "
by (frule i_closed[of "a"], rule l_div_eqn[of "\<rho> a" "x" "y"], assumption+)
                                        
lemma (in Group) tOp_assocTr41:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
       d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot> b \<cdot> c \<cdot> d = a \<cdot> b \<cdot> (c \<cdot> d)"
by (frule mult_closed[of "a" "b"], assumption+, 
                                   simp add:tassoc[of "a \<cdot> b" "c" "d"])

lemma (in Group) tOp_assocTr42:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
      d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot> b \<cdot> c \<cdot> d = a \<cdot> (b \<cdot> c)\<cdot> d"
by (simp add:tassoc[of "a" "b" "c"])

lemma (in Group) tOp_assocTr44:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;
      d \<in> carrier G \<rbrakk> \<Longrightarrow> (\<rho> a) \<cdot> b \<cdot> ((\<rho> c) \<cdot> d) = 
                                         (\<rho>  a) \<cdot> ((b \<cdot> (\<rho> c)) \<cdot> d)"  
apply (frule i_closed[of "a"],
       frule i_closed[of "c"])
apply (simp add:tassoc[of "b" "\<rho> c" "d"],
       frule mult_closed[of "\<rho> c" "d"], assumption+,
       simp add:tassoc[THEN sym, of "\<rho> a" "b" "(\<rho> c) \<cdot> d"])
done

lemma (in Group) tOp_assocTr45:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G; 
d \<in> carrier G\<rbrakk> \<Longrightarrow> a \<cdot> b \<cdot> c \<cdot> d = a \<cdot> (b \<cdot> (c \<cdot> d))"
apply (frule mult_closed[of "c" "d"], assumption+)
 apply (simp add:tassoc[of "a" "b" "c \<cdot> d", THEN sym])
 apply (simp add:tOp_assocTr41)
done
 
lemma (in Group) one_unique:"\<lbrakk>a \<in> carrier G; x \<in> carrier G;  x \<cdot> a = x\<rbrakk> \<Longrightarrow> 
                                a = \<one>"
apply (frule mult_closed[of "x" "a"], assumption+,
       frule i_closed[of "x"],
       frule l_mult_eqn[of "x \<cdot> a" "x" "\<rho> x"], assumption+)
apply (thin_tac "x \<cdot> a = x",
       simp add:tassoc[THEN sym, of "\<rho> x" "x" "a"],
       simp add:l_i l_unit)
done

lemma (in Group) i_one:"\<rho> \<one> = \<one>" 
by  (cut_tac unit_closed, frule l_i[of "\<one>"],
     frule i_closed[of "\<one>"], simp add:r_unit)

lemma (in Group) eqn_inv1:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; a = (\<rho> x) \<rbrakk> \<Longrightarrow> 
                       x = (\<rho> a)"
apply (frule i_closed[of "x"],
       frule l_mult_eqn[of "a" "\<rho> x" "x"], assumption+,
       thin_tac "a = \<rho> x", simp add:r_i,
       simp add:l_i_unique[of "a" "x"])
done

lemma (in Group) eqn_inv2:"\<lbrakk>a \<in> carrier G; x \<in> carrier G;  x \<cdot> a = x \<cdot> (\<rho> x)\<rbrakk> \<Longrightarrow>
                        x = (\<rho> a)"
apply (rule eqn_inv1, assumption+)
apply (rule l_div_eqn[of "x" "a" "\<rho> x"], assumption+,
       simp add:i_closed, assumption)
done

lemma (in Group) r_one_unique:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; a \<cdot> x = a\<rbrakk>  \<Longrightarrow>
                                 x = \<one>"
apply (frule mult_closed[of "a" "x"], assumption+,
       frule i_closed[of "a"],
       frule l_mult_eqn[of "a \<cdot> x" "a" "\<rho> a"], assumption+,
       thin_tac "a \<cdot> x = a",
       simp add:tassoc[THEN sym] l_i l_unit)
done

lemma (in Group) r_i_unique:"\<lbrakk>a \<in> carrier G; x \<in> carrier G; a \<cdot> x = \<one>\<rbrakk> \<Longrightarrow>
                             x = (\<rho> a)"
apply (cut_tac unit_closed,
       frule mult_closed[of "a" "x"], assumption+,
       frule i_closed[of "x"],
       frule r_mult_eqn[of "a \<cdot> x" "\<one>" "\<rho> x"], assumption+,
       thin_tac "a \<cdot> x = \<one>",
       simp add:tassoc[of "a" "x" "\<rho> x"] r_i r_unit l_unit) 
apply (simp add:eqn_inv1)
done

lemma (in Group) iop_i_i:"a \<in> carrier G  \<Longrightarrow> \<rho> (\<rho> a) = a"
apply (frule i_closed[of "a"], frule i_closed[of "\<rho> a"],
       frule l_i[of "\<rho> a"],
       frule mult_closed[of "\<rho> (\<rho> a)" "\<rho> a"], assumption+)
apply (cut_tac unit_closed,
       frule r_mult_eqn[of "\<rho> (\<rho> a) \<cdot> \<rho> a" "\<one>" "a"], assumption+,
       thin_tac "\<rho> (\<rho> a) \<cdot> \<rho> a = \<one>",
       simp only:tassoc) 
apply (simp add:l_i r_unit l_unit)
done

lemma (in Group) i_ab:"\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow>
                            \<rho> (a \<cdot> b) = (\<rho> b) \<cdot> (\<rho> a)"
apply (frule mult_closed[of "a" "b"], assumption+,
       frule i_closed[of "a \<cdot> b"],
       frule i_closed[of "a"], frule i_closed[of "b"],
       frule l_div_eqn[of "a \<cdot> b" "\<rho> (a \<cdot> b)" "(\<rho> b) \<cdot> (\<rho> a)"], assumption+,
       simp add:mult_closed, simp add:r_i[of "a \<cdot> b"],
       simp add:tOp_assocTr41[THEN sym], simp add:tOp_assocTr42,
       simp add:r_i r_unit)
apply assumption
done

lemma (in Group) sol_eq_l:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; x \<in> carrier G;
                   a \<cdot> x = b\<rbrakk> \<Longrightarrow> x = (\<rho> a) \<cdot> b"
apply (frule mult_closed[of "a" "x"], assumption+,
       frule i_closed[of "a"],
       frule l_mult_eqn[of "a \<cdot> x" "b" "\<rho> a"], assumption+)
apply (thin_tac "a \<cdot> x = b",
       simp add:tassoc[THEN sym],
       simp add:l_i l_unit)
done

lemma (in Group) sol_eq_r:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; x \<in> carrier G; 
       x \<cdot> a = b \<rbrakk> \<Longrightarrow>  x = b \<cdot> (\<rho> a)"
apply (frule mult_closed[of "x" "a"], assumption+,
       frule i_closed[of "a"],
       frule r_mult_eqn[of "x \<cdot> a" "b" "\<rho> a"], assumption+)
apply (thin_tac "x \<cdot> a = b",
       simp add:tassoc,
       simp add:r_i r_unit)
done
       
lemma (in Group) r_div_eq:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; a \<cdot> (\<rho> b) = \<one>\<rbrakk> \<Longrightarrow>
                            a = b"
apply (frule i_closed[of "b"],
       frule mult_closed[of "a" "\<rho> b"], assumption+,
       cut_tac unit_closed,
       frule r_mult_eqn[of "a \<cdot> (\<rho> b)" "\<one>" "b"], assumption+)
apply (thin_tac "a \<cdot> \<rho> b = \<one>",
       simp add:tassoc l_i r_i, simp add:l_unit r_unit)
done   

lemma (in Group) l_div_eq:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; (\<rho> a) \<cdot> b = \<one>\<rbrakk> \<Longrightarrow>
                               a = b"
apply (frule i_closed[of "a"],
       frule mult_closed[of "\<rho> a" "b"], assumption+,
       cut_tac unit_closed,
       frule l_mult_eqn[of "(\<rho> a) \<cdot> b" "\<one>" "a"], assumption+)
apply (thin_tac "\<rho> a \<cdot> b = \<one>",
       simp add:tassoc[THEN sym] r_i l_unit r_unit)
done

lemma (in Group) i_m_closed:"\<lbrakk>a \<in> carrier G ; b \<in> carrier G\<rbrakk> \<Longrightarrow>
              (\<rho> a) \<cdot> b \<in> carrier G "
by (rule mult_closed,
       simp add:i_closed, assumption)


section "Subgroups"

definition
  sg ::"[_ , 'a set ] \<Rightarrow> bool"  ("_ \<guillemotright> _ " [60, 61]60) where
  "G \<guillemotright> H \<longleftrightarrow> H \<noteq> {} \<and> H \<subseteq> carrier G \<and> (\<forall>a \<in> H. \<forall>b \<in> H. a \<cdot>\<^bsub>G\<^esub> (\<rho>\<^bsub>G\<^esub> b) \<in> H)" 
 
 (** SG is a set satisfying the condition above. In math textbooks this is 
  called a subgroup and it is also taken as a group with induced structure.**)

definition
   Gp :: "_ \<Rightarrow> 'a set \<Rightarrow> _"        ("(\<natural>\<index>_)" 70) where
   "\<natural>\<^bsub>G\<^esub>H \<equiv> G \<lparr> carrier := H, top := top G, iop := iop G, one := one G\<rparr>"     

  (** Gp G H is a group with carrier H, where H is sg **)


definition
  rcs :: "[_ , 'a set, 'a] \<Rightarrow> 'a set" (infix "\<bullet>\<index>" 70) where
  "H \<bullet>\<^bsub>G\<^esub> a = {b. \<exists> h \<in> H. h \<cdot>\<^bsub>G\<^esub> a = b}"

definition
  lcs :: "[_ , 'a, 'a set] \<Rightarrow> 'a set" (infix "\<diamondsuit>\<index>" 70) where
  "a \<diamondsuit>\<^bsub>G\<^esub> H = {b. \<exists> h \<in> H. a \<cdot>\<^bsub>G\<^esub> h = b}" 

definition
  nsg :: "_ \<Rightarrow> 'a set \<Rightarrow> bool"    ("_ \<triangleright> _" [60,61]60) where
  "G \<triangleright> H \<longleftrightarrow> G \<guillemotright> H \<and> (\<forall>x \<in> carrier G. H \<bullet>\<^bsub>G\<^esub> x = x \<diamondsuit>\<^bsub>G\<^esub> H)" 

definition
  set_rcs :: "[_ , 'a set] \<Rightarrow> 'a set set" where
  "set_rcs G H = {C. \<exists>a \<in> carrier G. C = H \<bullet>\<^bsub>G\<^esub> a}"

definition
  c_iop :: "[_ , 'a set]  \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "c_iop G H = (\<lambda>X\<in>set_rcs G H. {z. \<exists> x \<in> X . \<exists>h \<in> H. h \<cdot>\<^bsub>G\<^esub> (\<rho>\<^bsub>G\<^esub> x) = z})"      
 
definition
  c_top :: "[_, 'a set] \<Rightarrow> (['a set, 'a set] \<Rightarrow> 'a set)" where
  "c_top G H = (\<lambda>X\<in>set_rcs G H. \<lambda>Y\<in>set_rcs G H. 
    {z. \<exists>x \<in> X. \<exists> y \<in> Y. x \<cdot>\<^bsub>G\<^esub> y = z})" 

lemma (in Group) sg_subset:"G \<guillemotright> H \<Longrightarrow> H \<subseteq> carrier G"
by (simp add:sg_def)

lemma (in Group) one_Gp_one:"G \<guillemotright> H \<Longrightarrow> \<one>\<^bsub>(Gp G H)\<^esub> = \<one>"
by (simp add:Gp_def)

lemma (in Group) carrier_Gp:"G \<guillemotright> H \<Longrightarrow> (carrier (\<natural>H)) = H"
by (simp add:Gp_def)

lemma (in Group) sg_subset_elem:"\<lbrakk>G \<guillemotright> H; h \<in> H \<rbrakk> \<Longrightarrow> h \<in> carrier G"
by (frule sg_subset [of "H"], simp only:subsetD)

lemma (in Group) sg_mult_closedr:"\<lbrakk>G \<guillemotright> H; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow>
                x \<cdot> h \<in> carrier G"
apply (frule sg_subset_elem [of "H" "h"], assumption+)
apply (simp add:mult_closed)
done

lemma (in Group) sg_mult_closedl:"\<lbrakk>G \<guillemotright> H; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow>
                    h \<cdot> x \<in> carrier G"
apply (frule sg_subset_elem[of "H" "h"], assumption+)
apply (simp add:mult_closed)
done

lemma (in Group) sg_condTr1:"\<lbrakk>H \<subseteq> carrier G; H \<noteq> {};
                  \<forall>a. \<forall>b. a \<in> H \<and> b \<in> H \<longrightarrow>  a \<cdot> (\<rho> b) \<in> H\<rbrakk> \<Longrightarrow> \<one> \<in> H"
apply (frule  nonempty_ex [of "H"], erule exE)
apply (frule_tac x = x in spec,
       thin_tac "\<forall>a b. a \<in> H \<and> b \<in> H \<longrightarrow> a \<cdot> \<rho> b \<in> H",
       frule_tac x = x in spec,
       thin_tac "\<forall>b. x \<in> H \<and> b \<in> H \<longrightarrow> x \<cdot> \<rho> b \<in> H")
apply (frule_tac c = x in subsetD[of "H" "carrier G"], assumption+,
       simp add:r_i)
done

lemma (in Group) sg_unit_closed:"G \<guillemotright> H \<Longrightarrow> \<one> \<in> H"
apply (simp add:sg_def, (erule conjE)+,
       rule sg_condTr1, assumption+, blast)     
done

lemma (in Group) sg_i_closed:"\<lbrakk>G \<guillemotright> H; x \<in> H\<rbrakk> \<Longrightarrow> (\<rho> x) \<in> H"
apply (frule sg_unit_closed,
       frule sg_subset_elem[of "H" "x"], assumption,
       simp add:sg_def, (erule conjE)+)
apply (frule_tac x = \<one> in bspec, assumption,
       rotate_tac -1,
       frule_tac x = x in bspec, assumption,
       thin_tac "\<forall>b\<in>H. \<one> \<cdot> \<rho> b \<in> H",
       thin_tac "\<forall>a\<in>H. \<forall>b\<in>H. a \<cdot> \<rho> b \<in> H")
apply (frule i_closed[of "x"],
       simp add:l_unit)
done

lemma (in Group) sg_mult_closed:"\<lbrakk>G \<guillemotright> H; x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow>
                                       x \<cdot> y \<in> H" 
apply (frule sg_i_closed[of "H" "y"], assumption,
       simp add:sg_def, (erule conjE)+)
apply (frule_tac x = x in bspec, assumption,
       rotate_tac -1,
       frule_tac x = "\<rho> y" in bspec, assumption,
       thin_tac "\<forall>b\<in>H. x \<cdot> \<rho> b \<in> H",
       thin_tac "\<forall>a\<in>H. \<forall>b\<in>H. a \<cdot> \<rho> b \<in> H")
apply (frule subsetD[of "H" "carrier G"], assumption+,
      simp add:iop_i_i)
done

lemma (in Group) nsg_sg: "G \<triangleright> H \<Longrightarrow> G \<guillemotright> H"
by (simp add:nsg_def)

lemma (in Group) nsg_subset:"G \<triangleright> N  \<Longrightarrow> N \<subseteq> carrier G"
apply (simp add:nsg_def, (erule conjE)+)
apply (simp add:sg_subset)
done

lemma (in Group) nsg_lr_cst_eq:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                                     a \<diamondsuit> N = N \<bullet> a"
by (simp add: nsg_def)

lemma (in Group) sg_i_m_closed:"\<lbrakk>G \<guillemotright> H; a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> (\<rho> a) \<cdot> b \<in> H"
apply (rule sg_mult_closed, assumption+,
       simp add:sg_i_closed, assumption)
done

lemma (in Group) sg_m_i_closed:"\<lbrakk>G \<guillemotright> H; a \<in> H ; b \<in> H \<rbrakk> \<Longrightarrow> a \<cdot> (\<rho> b) \<in> H"
apply (simp add:sg_def)
done

definition
  sg_gen :: "[_ , 'a set] \<Rightarrow> 'a set" where
  "sg_gen G A = \<Inter>{H. G \<guillemotright> H \<and> A \<subseteq> H}"

lemma (in Group) smallest_sg_gen:"\<lbrakk>A \<subseteq> carrier G; G \<guillemotright> H; A \<subseteq> H\<rbrakk> \<Longrightarrow>
                                   sg_gen G A \<subseteq> H"
apply (simp add:sg_gen_def)
apply auto
done

lemma (in Group) special_sg_G: "G \<guillemotright> (carrier G)"
apply (simp add:sg_def,
       cut_tac unit_closed, simp add:nonempty)
apply ((rule ballI)+, simp add:mult_closed i_closed)
done

lemma (in Group) special_sg_self: "G = \<natural>(carrier G)"
by (simp add:Gp_def)

lemma (in Group) special_sg_e: "G \<guillemotright> {\<one>}"
apply (simp add:sg_def)
apply (simp add:unit_closed i_one l_unit)
done

lemma (in Group) inter_sgs:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K\<rbrakk> \<Longrightarrow> G \<guillemotright> (H \<inter> K)"
apply (frule sg_unit_closed[of "H"],
       frule sg_unit_closed[of "K"])
apply (simp add:sg_def)
apply auto
done

lemma (in Group) subg_generated:"A \<subseteq> carrier G  \<Longrightarrow> G \<guillemotright> (sg_gen G A)"
apply (simp add:sg_def)
apply (rule conjI,
       simp add:sg_gen_def,
       rule ex_nonempty, simp)
 apply (rule contrapos_pp, simp+,
        frule_tac x = \<one> in spec,
        thin_tac "\<forall>x. \<exists>xa. G \<guillemotright> xa  \<and> A \<subseteq> xa \<and> x \<notin> xa",
        erule exE, (erule conjE)+,
        frule_tac H = x in sg_unit_closed, simp)

apply (rule conjI)
 apply (cut_tac special_sg_G,
        simp add:sg_gen_def,
        rule subsetI,
        blast)

apply ((rule ballI)+,
       simp add:sg_gen_def,
       rule allI, rule impI,
       frule_tac a = x in forall_spec, assumption,
       thin_tac "\<forall>x. G \<guillemotright> x  \<and> A \<subseteq> x \<longrightarrow> a \<in> x",
       frule_tac a = x in forall_spec, assumption,
       thin_tac "\<forall>x. G \<guillemotright> x  \<and> A \<subseteq> x \<longrightarrow> b \<in> x")
 apply (simp add:sg_m_i_closed)
done

definition
  Qg :: "[_ , 'a set] \<Rightarrow> 
         \<lparr>carrier:: 'a set set, top:: ['a set, 'a set] \<Rightarrow> 'a set,
           iop:: 'a set \<Rightarrow> 'a set, one:: 'a set \<rparr>" where
  "Qg G H = \<lparr>carrier = set_rcs G H, top = c_top G H, iop = c_iop G H, one = H \<rparr>"


definition
  Pj :: "[_ , 'a set] \<Rightarrow>  ( 'a => 'a set)" where
  "Pj G H = (\<lambda>x \<in> carrier G. H \<bullet>\<^bsub>G\<^esub> x)"        

no_notation inverse_divide (infixl "'/" 70)

abbreviation
  QGRP :: "([('a, 'more) Group_scheme, 'a set] => ('a set) Group)"
    (infixl "'/" 70) where
  "G / H == Qg G H"
  

definition
  gHom ::"[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme] \<Rightarrow> 
           ('a  \<Rightarrow> 'b) set" where
  "gHom G F = {f. (f \<in> extensional (carrier G) \<and> f \<in> carrier G \<rightarrow> carrier F) \<and>
       (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. f (x \<cdot>\<^bsub>G\<^esub> y) = (f x) \<cdot>\<^bsub>F\<^esub> (f y))}"
 
definition
  gkernel ::"[('a, 'more) Group_scheme , ('b, 'more1) Group_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> 'a set" where
  "gkernel G F f = {x. (x \<in> carrier G) \<and> (f x = \<one>\<^bsub>F\<^esub>)}"


definition
  iim :: "[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme, 'a \<Rightarrow> 'b, 
            'b set]  \<Rightarrow> 'a set" where
  "iim G F f K = {x. (x \<in> carrier G) \<and> (f x \<in> K)}"

abbreviation
  GKER :: "[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme, 'a \<Rightarrow> 'b ] \<Rightarrow> 'a set"
    ("(3gker\<^bsub>_,_\<^esub> _)" [88,88,89]88) where
  "gker\<^bsub>G,F\<^esub> f == gkernel G F f"

definition
  gsurjec :: "[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme, 
             'a \<Rightarrow> 'b] \<Rightarrow> bool"  ("(3gsurj\<^bsub>_,_\<^esub> _)" [88,88,89]88) where
  "gsurj\<^bsub>F,G\<^esub> f \<longleftrightarrow> f \<in> gHom F G \<and> surj_to f (carrier F) (carrier G)" 


definition
  ginjec :: "[('a, 'more) Group_scheme, ('b, 'more1) Group_scheme, 
             'a \<Rightarrow> 'b]  \<Rightarrow> bool"    ("(3ginj\<^bsub>_,_\<^esub> _)" [88,88,89]88) where
  "ginj\<^bsub>F,G\<^esub> f \<longleftrightarrow> f \<in> gHom F G \<and> inj_on f (carrier F)"

definition
  gbijec :: "[('a, 'm) Group_scheme, ('b, 'm1) Group_scheme, 'a \<Rightarrow> 'b]
             \<Rightarrow> bool"       ("(3gbij\<^bsub>_,_\<^esub> _)" [88,88,89]88) where
  "gbij\<^bsub>F,G\<^esub> f \<longleftrightarrow> gsurj\<^bsub>F,G\<^esub> f \<and> ginj\<^bsub>F,G\<^esub> f"

definition
  Ug :: "_  \<Rightarrow>  ('a, 'more) Group_scheme" where
  "Ug G = \<natural>\<^bsub>G\<^esub> {\<one>\<^bsub>G\<^esub>}"

definition
  Ugp :: "_ \<Rightarrow> bool" where
  "Ugp G == Group G \<and> carrier G = {\<one>\<^bsub>G\<^esub>}"

definition
  isomorphic :: "[('a, 'm) Group_scheme, ('b, 'm1) Group_scheme]
                         \<Rightarrow> bool"   (infix "\<cong>" 100) where
  "F \<cong> G \<longleftrightarrow> (\<exists>f. gbij\<^bsub>F,G\<^esub> f)"

definition
  constghom :: "[('a, 'm) Group_scheme, ('b, 'm1) Group_scheme] 
                           \<Rightarrow> ('a \<Rightarrow> 'b)"  ("('1'\<^bsub>_,_\<^esub>)" [88,89]88) where
  "1\<^bsub>F,G\<^esub> = (\<lambda>x\<in>carrier F. \<one>\<^bsub>G\<^esub>)" 

definition
  cmpghom :: "[('a, 'm) Group_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c" where
  "cmpghom F g f = compose (carrier F) g f"  

abbreviation
  GCOMP :: "['b \<Rightarrow> 'c, ('a, 'm) Group_scheme, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c"
    ("(3_ \<circ>\<^bsub>_\<^esub> _)" [88, 88, 89]88) where
  "g \<circ>\<^bsub>F\<^esub> f == cmpghom F g f"

lemma Group_Ugp:"Ugp G \<Longrightarrow> Group G"
by (simp add:Ugp_def)

lemma (in Group) r_mult_in_sg:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> carrier G; x \<cdot> a \<in> H\<rbrakk>
                              \<Longrightarrow> \<exists>h \<in> H. h \<cdot> (\<rho> a) = x"
apply (frule inEx[of "x \<cdot> a" "H"],
       erule bexE)
apply (rotate_tac -1, frule sym, thin_tac "y = x \<cdot> a",
       frule_tac h = y in sg_subset_elem[of "H"], assumption+,
       frule_tac b1 = y in sol_eq_r[THEN sym, of "a" _ "x"], assumption+)
apply blast
done  

lemma (in Group) r_unit_sg:"\<lbrakk>G \<guillemotright> H; h \<in> H\<rbrakk> \<Longrightarrow> h \<cdot> \<one> = h"
by (frule sg_subset_elem [of "H" "h"], assumption,
       simp add:r_unit)

lemma (in Group) sg_l_unit:"\<lbrakk>G \<guillemotright> H; h \<in> H\<rbrakk> \<Longrightarrow> \<one> \<cdot> h = h"
by (frule sg_subset_elem [of "H" "h"], assumption+, simp add:l_unit)

lemma (in Group) sg_l_i:"\<lbrakk>G \<guillemotright> H; x \<in> H \<rbrakk> \<Longrightarrow> (\<rho> x) \<cdot> x = \<one>"
by (frule sg_subset_elem[of "H" "x"], assumption+,
       simp add:l_i)

lemma (in Group) sg_tassoc:"\<lbrakk>G \<guillemotright> H; x \<in> H; y \<in> H; z \<in> H\<rbrakk> \<Longrightarrow>
                  x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)" 
apply (frule sg_subset_elem[of "H" "x"], assumption+,
       frule sg_subset_elem[of "H" "y"], assumption+,
       frule sg_subset_elem[of "H" "z"], assumption+)
apply (simp add:tassoc)
done

lemma (in Group) sg_condition:"\<lbrakk>H \<subseteq> carrier G; H \<noteq> {};
       \<forall>a. \<forall>b. a \<in> H \<and> b \<in> H \<longrightarrow>  a \<cdot> (\<rho> b) \<in> H\<rbrakk> \<Longrightarrow> G \<guillemotright> H"
by (simp add:sg_def)

definition
  Gimage :: "[('a, 'm) Group_scheme, ('b, 'm1) Group_scheme, 'a  \<Rightarrow> 'b] \<Rightarrow>
                         ('b, 'm1) Group_scheme" where
  "Gimage F G f = Gp G (f `(carrier F))"
  
abbreviation
  GIMAGE :: "[('a, 'm) Group_scheme, ('b, 'm1) Group_scheme,
        'a \<Rightarrow> 'b ] \<Rightarrow> ('b, 'm1) Group_scheme"    ("(3Img\<^bsub>_,_\<^esub> _)" [88,88,89]88) where
  "Img\<^bsub>F,G\<^esub> f == Gimage F G f"

lemma (in Group) Group_Gp:"G \<guillemotright> H \<Longrightarrow> Group (\<natural> H)" 
apply (simp add:Group_def Gp_def)
apply (simp add:sg_tassoc sg_l_i sg_unit_closed sg_l_unit
         sg_mult_closed sg_i_closed)
done
 
lemma (in Group) Gp_carrier:"G \<guillemotright> H \<Longrightarrow> carrier (Gp G H) = H" 
by (simp add:Gp_def)

lemma (in Group) sg_sg:"\<lbrakk>G \<guillemotright> K; G \<guillemotright> H; H \<subseteq> K\<rbrakk> \<Longrightarrow> Gp G K \<guillemotright> H"
apply (simp add:sg_def [of "Gp G K" "H"])
apply (rule conjI, simp add:sg_def)
 apply (simp add:Gp_def)
 apply ((rule ballI)+, simp add:sg_m_i_closed)
done

lemma (in Group) sg_subset_of_subG:"\<lbrakk>G \<guillemotright> K; Gp G K \<guillemotright> H\<rbrakk> \<Longrightarrow> H \<subseteq> K"
by (simp add:sg_def[of "\<natural> K"], simp add:Gp_def)

lemma const_ghom:"\<lbrakk>Group F; Group G\<rbrakk> \<Longrightarrow> 1\<^bsub>F,G\<^esub> \<in> gHom F G"
apply (simp add:gHom_def constghom_def)
apply (simp add:Pi_def Group.unit_closed)
apply ((rule ballI)+, 
       cut_tac Group.unit_closed[of "G"],
       simp add:Group.mult_closed Group.l_unit)
apply assumption
done

lemma (in Group) const_gbij:"gbij\<^bsub>(\<natural> {\<one>}),(\<natural> {\<one>})\<^esub> (1\<^bsub>(\<natural>{\<one>}),(\<natural>{\<one>})\<^esub>)"
apply (cut_tac special_sg_e,
       frule Group_Gp[of "{\<one>}"],
       frule const_ghom[of "\<natural> {\<one>}" "\<natural> {\<one>}"], assumption)
apply (simp add:gbijec_def)
apply (rule conjI, simp add:gsurjec_def,
       simp add:surj_to_def Gp_def constghom_def) 
apply (simp add:ginjec_def inj_on_def Gp_def)
done

lemma (in Group) unit_Groups_isom:" (\<natural> {\<one>}) \<cong> (\<natural> {\<one>})" 
apply (unfold isomorphic_def,
       cut_tac const_gbij, blast)
done

lemma Ugp_const_gHom:"\<lbrakk>Ugp G; Ugp E\<rbrakk> \<Longrightarrow> (\<lambda>x\<in>carrier G. \<one>\<^bsub>E\<^esub>) \<in> gHom G E"
apply (simp add:gHom_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Group.unit_closed[of "E"] Ugp_def) 
 apply (simp add:Ugp_def, (erule conjE)+)
 apply (cut_tac Group.unit_closed[of "G"], cut_tac Group.unit_closed[of "E"])
 apply (simp add:Group.l_unit) apply assumption+
done

lemma Ugp_const_gbij:"\<lbrakk>Ugp G; Ugp E\<rbrakk> \<Longrightarrow> gbij\<^bsub>G,E\<^esub> (\<lambda>x\<in>carrier G. \<one>\<^bsub>E\<^esub>)"
apply (simp add:gbijec_def)
apply (simp add:gsurjec_def ginjec_def)
apply (simp add:Ugp_const_gHom)
apply (rule conjI)
apply (simp add:surj_to_def, simp add:Ugp_def)

apply (simp add:inj_on_def)
apply ((rule ballI)+, simp add:Ugp_def)
done
                       

lemma Ugps_isomorphic:"\<lbrakk>Ugp G; Ugp E\<rbrakk> \<Longrightarrow> G \<cong> E"
apply (simp add:isomorphic_def)
apply (frule_tac Ugp_const_gbij[of "G" "E"], assumption+)
apply blast
done

lemma (in Group) Gp_mult_induced:"\<lbrakk>G \<guillemotright> L; a \<in> L; b \<in> L\<rbrakk>  \<Longrightarrow>  
                          a \<cdot>\<^bsub>(Gp G L)\<^esub> b = a \<cdot> b"
by (simp add:Gp_def)

lemma (in Group) sg_i_induced:"\<lbrakk>G \<guillemotright> L; a \<in> L\<rbrakk>  \<Longrightarrow> \<rho>\<^bsub>(Gp G L)\<^esub> a = \<rho> a"
by (simp add:Gp_def)

lemma (in Group) Gp_mult_induced1:"\<lbrakk>G \<guillemotright> H ; G \<guillemotright> K; a \<in> H \<inter> K; b \<in> H \<inter> K\<rbrakk> 
          \<Longrightarrow> a \<cdot>\<^bsub>\<natural>(H \<inter> K)\<^esub> b = a \<cdot>\<^bsub>(\<natural>H)\<^esub> b"
by (simp add:Gp_def)

lemma (in Group) Gp_mult_induced2:"\<lbrakk>G \<guillemotright> H ; G \<guillemotright> K; a \<in> H \<inter> K; b \<in> H \<inter> K\<rbrakk> 
          \<Longrightarrow> a \<cdot>\<^bsub>\<natural>(H \<inter> K)\<^esub> b = a \<cdot>\<^bsub>(\<natural>K)\<^esub> b"
by (simp add:Gp_def)

lemma (in Group) sg_i_induced1:"\<lbrakk>G \<guillemotright> H ; G \<guillemotright> K; a \<in> H \<inter> K\<rbrakk> 
                                     \<Longrightarrow>  \<rho>\<^bsub>\<natural>(H \<inter> K)\<^esub> a = \<rho>\<^bsub>(\<natural>H)\<^esub> a"
by (simp add:Gp_def)

lemma (in Group) sg_i_induced2:"\<lbrakk>G \<guillemotright> H ; G \<guillemotright> K; a \<in> H \<inter> K\<rbrakk> 
          \<Longrightarrow>  \<rho>\<^bsub>\<natural>(H \<inter> K)\<^esub> a = \<rho>\<^bsub>\<natural>K\<^esub> a"
by (simp add:Gp_def)

lemma (in Group) subg_sg_sg:"\<lbrakk>G \<guillemotright> K; (Gp G K) \<guillemotright> H \<rbrakk> \<Longrightarrow> G \<guillemotright> H" 
apply (frule sg_subset_of_subG[of "K" "H"], assumption+,
       simp add:sg_def [of _ "H"])
apply (simp add:Gp_def[of _ "K"],
       frule sg_subset[of "K"], simp add:subset_trans[of "H" "K" "carrier G"])
done 

lemma (in Group) Gp_inherited:"\<lbrakk>G \<guillemotright> K; G \<guillemotright> L; K \<subseteq> L\<rbrakk> \<Longrightarrow> 
                                Gp (Gp G L) K = Gp G K" 
by (simp add:Gp_def)

section "Cosets"

(* left cosets *)
lemma (in Group) mem_lcs:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> a \<diamondsuit> H\<rbrakk>  \<Longrightarrow> 
                          x \<in> carrier G"
by (simp add: lcs_def, erule bexE,
       frule_tac h = h in sg_mult_closedr[of "H" "a"], assumption+, simp)

lemma (in Group) lcs_subset:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G\<rbrakk> \<Longrightarrow> a \<diamondsuit> H \<subseteq> carrier G"
apply (simp add:lcs_def,
       rule subsetI, simp, erule bexE)
apply (frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       frule_tac a = a and b = h in mult_closed, assumption+)
apply simp
done

lemma (in Group) a_in_lcs:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G\<rbrakk> \<Longrightarrow> a \<in> a \<diamondsuit> H"
apply (simp add: lcs_def,
       rule bexI [of _ "\<one>"],
       subst r_unit, assumption+, simp)
apply (simp add:sg_unit_closed)
done

lemma (in Group) eq_lcs1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
         x \<in> a \<diamondsuit> H; a \<diamondsuit> H = b \<diamondsuit> H\<rbrakk> \<Longrightarrow>  x \<in> b \<diamondsuit> H"
by simp

lemma (in Group) eq_lcs2:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
                            a \<diamondsuit> H = b \<diamondsuit> H\<rbrakk> \<Longrightarrow> a \<in> b \<diamondsuit> H"
by (frule a_in_lcs[of "H" "a"], assumption+, simp)
 
lemma (in Group) lcs_mem_ldiv:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
                                  (a \<in> b \<diamondsuit> H) = ((\<rho> b) \<cdot> a \<in> H)"
apply (rule iffI)
apply (simp add: lcs_def, erule bexE)
apply (frule_tac x = h in sol_eq_l[of "b" "a"], assumption+,
       simp add:sg_subset_elem[of "H"], assumption+) 
apply (thin_tac "b \<cdot> h = a", simp)

apply (frule_tac x = "(\<rho> b) \<cdot> a" and A = H in inEx,
       erule bexE,
       frule_tac h = y in sg_subset_elem[of "H"], assumption+,
       frule sg_subset_elem[of "H" "(\<rho> b) \<cdot> a"], assumption+)
apply (frule_tac a = y in l_mult_eqn[of _ "(\<rho> b) \<cdot> a" "b"], assumption+,
       frule i_closed[of "b"],
       thin_tac "y = \<rho> b \<cdot> a",
       simp add:tassoc[THEN sym], simp add:r_i l_unit)
apply (rotate_tac -2, frule sym, thin_tac "b \<cdot> y = a", simp add:lcs_def,
       blast)
done

(*
lemma (in Group) lcsTr4:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
 x \<in> carrier G\<rbrakk> \<Longrightarrow> (i ((i a) \<cdot> b)) \<cdot> ((i a) \<cdot> x) = (i b) \<cdot> x"
apply (frule i_closed[of "a"], frule i_closed[of "b"],
       simp add:i_ab[of "i a" "b"])
apply (frule mult_closed[of "i a" "x"], assumption+,
       simp add:iop_i_i,
       simp add:tassoc[of "i b" "a" "(i a) \<cdot> x"],
       simp add:tassoc[THEN sym, of "a" "i a" "x"] r_i l_unit)
done *)

lemma (in Group) lcsTr5:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
                 (\<rho> a) \<cdot> b \<in> H; x \<in> a \<diamondsuit> H\<rbrakk> \<Longrightarrow> ((\<rho> b) \<cdot> x) \<in> H"
apply (frule mem_lcs[of "H" "a" "x"], assumption+,
       subst lcs_mem_ldiv[THEN sym, of "H" "x" "b"], assumption+,
       simp add:lcs_def, erule bexE)
apply (frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       frule_tac x = h in sol_eq_l[of "a" "x"], assumption+,
       frule sg_i_m_closed[of "H" "(\<rho> a) \<cdot> b" "(\<rho> a) \<cdot> x"], assumption+,
       rotate_tac -1, frule sym, thin_tac "h = \<rho> a \<cdot> x", simp)
apply (frule i_closed[of "a"],
       simp add:i_ab iop_i_i, frule i_closed[of "b"],
       simp add:tassoc[of "\<rho> b" "a"],
       simp add:tassoc[THEN sym, of "a" "\<rho> a" "x"] r_i l_unit)
apply (frule inEx[of "(\<rho> b) \<cdot> x"], erule bexE,
       rotate_tac -1, frule sym, thin_tac "y = \<rho> b \<cdot> x",
       frule_tac b = y in sol_eq_l[of "\<rho> b" _ "x"],
       simp add:sg_subset_elem, assumption+,
       simp add:iop_i_i, blast)
done

lemma (in Group) lcsTr6:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
                         (\<rho> a) \<cdot> b \<in> H; x \<in> a \<diamondsuit> H\<rbrakk> \<Longrightarrow>  x \<in> b \<diamondsuit> H"
by (frule lcsTr5[of "H" "a" "b" "x"], assumption+,
       subst lcs_mem_ldiv, assumption+, rule mem_lcs, assumption+)

lemma (in Group) lcs_Unit1:"G \<guillemotright> H \<Longrightarrow> \<one> \<diamondsuit> H = H"
apply (rule equalityI)
apply (rule subsetI, simp add:lcs_def, erule bexE,
       frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       simp add:l_unit)
apply (rule subsetI,
       simp add:lcs_def,
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       frule_tac a = x in l_unit)
apply blast
done

lemma (in Group) lcs_Unit2:"\<lbrakk>G \<guillemotright> H; h \<in> H\<rbrakk> \<Longrightarrow> h \<diamondsuit> H = H"
apply (rule equalityI)
apply (rule subsetI, simp add:lcs_def, erule bexE,
       frule_tac x = h and y = ha in sg_mult_closed, assumption+, simp)
apply (rule subsetI,
       simp add:lcs_def,
       rule_tac  x = "(\<rho> h) \<cdot> x" in bexI[of _ _ "H"])
apply (frule sg_subset_elem[of "H" "h"], assumption+,
       frule i_closed[of "h"],
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       simp add:tassoc[THEN sym, of "h" "\<rho> h"] r_i l_unit)
apply (simp add:sg_i_m_closed[of "H" "h"])
done

lemma (in Group) lcsTr7:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G; (\<rho> a) \<cdot> b \<in> H\<rbrakk>
                        \<Longrightarrow> a \<diamondsuit> H \<subseteq>  b \<diamondsuit> H"
apply (rule subsetI)
apply (simp add:lcsTr6 [of "H" "a" "b" _])
done

lemma (in Group) lcsTr8:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> h \<in> a \<diamondsuit> H"
apply (simp add:lcs_def)
apply blast
done

lemma (in Group) lcs_tool1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
      (\<rho> a) \<cdot> b \<in> H\<rbrakk> \<Longrightarrow> (\<rho> b) \<cdot> a \<in> H"
by (frule sg_i_closed [of "H" "(\<rho> a) \<cdot> b"], assumption+,
       frule i_closed[of "a"], simp add:i_ab iop_i_i)

theorem (in Group) lcs_eq:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
           ((\<rho> a) \<cdot> b \<in> H) = (a \<diamondsuit> H = b \<diamondsuit> H)" 
apply (rule iffI)
 apply ((rule equalityI),
        (rule lcsTr7 [of "H" "a" "b"], assumption+),
        (frule lcs_tool1 [of "H" "a" "b"], assumption+),
        (rule lcsTr7 [of "H" "b" "a"], assumption+))
apply (subst lcs_mem_ldiv[THEN sym, of "H" "b" "a"], assumption+,
       simp add:a_in_lcs[of "H" "b"])
done

lemma (in Group) rcs_subset:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G\<rbrakk> \<Longrightarrow> H \<bullet> a \<subseteq> carrier G"
apply (rule subsetI,
       simp add:rcs_def, erule bexE,
       frule_tac h = h in sg_mult_closedl[of "H" "a"], assumption+)
apply simp
done

lemma (in Group) mem_rcs:"\<lbrakk>G \<guillemotright> H; x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. h \<cdot> a = x" 
by (simp add:rcs_def)

lemma (in Group) rcs_subset_elem:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> H \<bullet> a\<rbrakk>  \<Longrightarrow> 
                                                        x \<in> carrier G"
apply (simp add:rcs_def, erule bexE)
apply (frule_tac h = h in sg_mult_closedl[of "H" "a"], assumption+,
       simp)
done

lemma (in Group) rcs_in_set_rcs:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G\<rbrakk> \<Longrightarrow> 
          H \<bullet> a \<in> set_rcs G H"
apply (simp add:set_rcs_def)
apply blast
done

lemma (in Group) rcsTr0:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow>
                         H \<bullet> (a \<cdot> b) \<in> set_rcs G H"
apply (rule rcs_in_set_rcs [of "H" "a \<cdot> b"], assumption)
apply (simp add:mult_closed)
done

lemma (in Group) a_in_rcs:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G\<rbrakk> \<Longrightarrow> a \<in> H \<bullet> a"
apply (simp add: rcs_def)
apply (frule l_unit[of "a"],
       frule sg_unit_closed[of "H"], blast)
done

lemma (in Group) rcs_nonempty:"\<lbrakk>G \<guillemotright> H; X \<in> set_rcs G H\<rbrakk> \<Longrightarrow> X \<noteq> {}"
apply (simp add:set_rcs_def, erule bexE)
apply (frule_tac a = a in a_in_rcs[of "H"], assumption+, simp)
apply (simp add:nonempty)
done

lemma (in Group) rcs_tool0:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
      a \<cdot> (\<rho> b) \<in> H\<rbrakk> \<Longrightarrow> b \<cdot> (\<rho> a) \<in> H"
by (frule sg_i_closed [of "H" "a \<cdot> ( \<rho> b)"], assumption+,
       frule i_closed[of "b"], simp add:i_ab iop_i_i)

lemma (in Group) rcsTr1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
         x \<in> H \<bullet> a; H \<bullet> a = H \<bullet> b\<rbrakk> \<Longrightarrow> x \<in> H \<bullet> b"
by simp

lemma (in Group) rcs_eqTr:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
                             H \<bullet> a = H \<bullet> b\<rbrakk> \<Longrightarrow> a \<in> H \<bullet> b"
apply (rule rcsTr1, assumption+)
apply (rule a_in_rcs, assumption+)
done 

lemma (in Group) rcs_eqTr1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
           (a \<in> H \<bullet> b) =  (a \<cdot> (\<rho> b) \<in> H)"
apply (rule iffI)
apply (simp add:rcs_def, erule bexE,
       frule_tac h = h in sg_subset_elem[of "H"], assumption+)
apply (frule_tac x = h in sol_eq_r[of "b" "a" _], assumption+, simp)
apply (frule inEx[of "a \<cdot> (\<rho> b)" "H"], erule bexE)
apply (frule_tac h = y in sg_subset_elem[of "H"], assumption+,
       frule i_closed[of "b"])
apply (rotate_tac -3, frule sym, thin_tac "y = a \<cdot> \<rho> b",
       frule_tac b = y in sol_eq_r[of "\<rho> b" _ "a"], assumption+,
       simp add:iop_i_i)
apply (simp add:rcs_def, blast)
done   
       
lemma (in Group) rcsTr2:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> H \<bullet> (\<rho> a)\<rbrakk> \<Longrightarrow> 
                          b \<cdot> a \<in> H" 
apply (frule i_closed[of "a"],
       frule_tac rcs_subset_elem[of "H" "\<rho> a" "b"], assumption+,
       frule rcs_eqTr1[of "H" "b" "\<rho> a"], assumption+)
apply (simp add:iop_i_i)
done

lemma (in Group) rcsTr5:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
       b \<cdot> (\<rho> a) \<in> H; x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow> x \<cdot> (\<rho> b) \<in> H"
apply (frule rcs_subset_elem[of "H" "a" "x"], assumption+,
       simp add:rcs_def, erule bexE)
apply (frule_tac h = h in sg_subset_elem[of "H"], assumption,
       frule_tac a = h and b = a in mult_closed, assumption+,
       frule i_closed[of "b"])
apply (frule_tac a = "h \<cdot> a" in r_mult_eqn[of _ "x" "\<rho> b"], assumption+,
       thin_tac "h \<cdot> a = x",
       simp add:tassoc[of _ "a" "\<rho> b"],
       frule_tac x = h in sg_mult_closed[of "H" _ "a \<cdot> (\<rho> b)"], assumption+,
       rule rcs_tool0[of "H" "b" "a"], assumption+)
apply simp
done

lemma (in Group) rcsTr6:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G;
                  b \<cdot> (\<rho> a) \<in> H ; x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow> x \<in> H \<bullet> b"
apply (frule  rcsTr5 [of "H" "a" "b" "x"], assumption+)
apply (subst rcs_eqTr1[of "H" "x" "b"], assumption+)
apply (rule rcs_subset_elem[of "H" "a" "x"], assumption+)
done

lemma (in Group) rcs_Unit1:"G \<guillemotright> H \<Longrightarrow>  H \<bullet> \<one> = H"
apply (rule equalityI)
apply (rule subsetI,
       simp add:rcs_def, erule bexE,
       frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       simp add:r_unit)
apply (rule subsetI)
apply (simp add:rcs_def,
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       frule_tac a = x in r_unit, blast)
done

lemma (in Group) unit_rcs_in_set_rcs:"G \<guillemotright> H \<Longrightarrow> H \<in> set_rcs G H"
apply (cut_tac unit_closed)
apply (frule rcs_in_set_rcs[of "H" "\<one>"], assumption+)
apply (simp add:rcs_Unit1)
done

lemma (in Group) rcs_Unit2:"\<lbrakk>G \<guillemotright> H; h \<in> H\<rbrakk> \<Longrightarrow> H \<bullet> h = H"
apply (rule equalityI)
 apply (rule subsetI,
        simp add:rcs_def, erule bexE,
        frule_tac x = ha and y = h in sg_mult_closed[of "H"], assumption+,
        simp)

apply (rule subsetI,
       simp add:rcs_def)
apply (frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       frule i_closed[of "h"],
       frule_tac a = x in tassoc[of _ "\<rho> h" "h"], assumption+,
       simp add:l_i r_unit)
apply (frule_tac a = x in sg_m_i_closed[of "H" _ "h"], assumption+,
       blast)
done
     
lemma (in Group) rcsTr7:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G; b \<cdot> (\<rho> a) \<in> H\<rbrakk>
                         \<Longrightarrow> H \<bullet> a  \<subseteq>  H \<bullet> b"
apply (rule subsetI)
apply (rule rcsTr6[of "H" "a" "b"], assumption+)
done 

lemma (in Group) rcs_tool1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G; 
      b \<cdot> (\<rho> a) \<in> H\<rbrakk> \<Longrightarrow>  a \<cdot> (\<rho> b) \<in> H "
apply (frule sg_i_closed[of "H" "b \<cdot> (\<rho> a)"], assumption+)
 apply (frule i_closed[of "a"], simp add:i_ab iop_i_i)
done

lemma (in Group) rcs_tool2:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G;  x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow>
                               \<exists> h \<in> H. h \<cdot> a = x"
apply (simp add:rcs_def)
done

theorem (in Group) rcs_eq:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow>
                            (b \<cdot> (\<rho> a) \<in> H) = (H \<bullet> a = H \<bullet> b)"
apply (rule iffI)
apply (rule equalityI)
apply (frule rcsTr7[of "H" "a" "b"], assumption+)
apply (frule rcs_tool1[of "H" "a" "b"], assumption+)
apply (rule rcsTr7[of "H" "b" "a"], assumption+)
apply (frule a_in_rcs[of "H" "a"], assumption, simp)
apply (simp add:rcs_eqTr1[of "H" "a" "b"])
apply (rule rcs_tool1, assumption+)
done

lemma (in Group) rcs_eq1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow>
                                           H \<bullet> a = H \<bullet> x"
apply (frule rcs_subset_elem[of "H" "a" "x"], assumption+)
apply (subst rcs_eq[THEN sym, of "H" "a" "x"], assumption+)
apply (subst rcs_eqTr1[THEN sym, of "H" "x" "a"], assumption+)
done

lemma (in Group) rcs_eq2:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G;  b \<in> carrier G; 
                           (H \<bullet> a) \<inter> (H \<bullet> b) \<noteq> {}\<rbrakk> \<Longrightarrow> (H \<bullet> a) = (H \<bullet> b)"
apply (frule nonempty_int [of "H \<bullet> a" "H \<bullet> b"], erule exE)
apply (simp, erule conjE)
apply (frule_tac x = x in rcs_eq1[of "H" "a"], assumption+,
       frule_tac x = x in rcs_eq1[of "H" "b"], assumption+)
apply simp
done

lemma (in Group) rcs_meet:"\<lbrakk>G \<guillemotright> H; X \<in> set_rcs G H; Y \<in> set_rcs G H;
                               X \<inter> Y \<noteq> {}\<rbrakk> \<Longrightarrow> X = Y"
apply (simp add:set_rcs_def, (erule bexE)+, simp)
apply (rule_tac a = a and b = aa in rcs_eq2[of "H"], assumption+)
done
      
lemma (in Group) rcsTr8:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; h \<in> H; x \<in> H \<bullet> a\<rbrakk> \<Longrightarrow>
                      h \<cdot> x \<in> H \<bullet> a"
apply (frule rcs_subset_elem[of "H" "a" "x"], assumption+,
       frule sg_subset_elem[of "H" "h"], assumption+)
apply (simp add:rcs_def, erule bexE,
       frule_tac h = ha in sg_subset_elem[of "H"], assumption+,
       frule_tac a = ha and b = a in mult_closed, assumption,
       frule_tac a = "ha \<cdot> a" and b = x and c = h in l_mult_eqn, assumption+,
       thin_tac "ha \<cdot> a = x", simp add:tassoc[THEN sym, of "h" _ "a"])
apply (frule_tac x = h and y = ha in sg_mult_closed[of "H"], assumption+,
       blast)
done

lemma (in Group) rcsTr9:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; h \<in> H; (\<rho> x) \<in> H \<bullet> a\<rbrakk> \<Longrightarrow>
                          h \<cdot> (\<rho> x) \<in> H \<bullet> a"
by (insert rcsTr8 [of "H" "a" "h" "\<rho> x"], simp)

lemma (in Group) rcsTr10:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> H \<bullet> a; y \<in> H \<bullet> a\<rbrakk> \<Longrightarrow>
                          x \<cdot> (\<rho> y) \<in> H" 
apply (simp add:rcs_def)
apply (erule bexE)+
apply (rotate_tac -1, frule sym, thin_tac "ha \<cdot> a = y",
       frule sym, thin_tac "h \<cdot> a = x", simp,
       thin_tac "y = ha \<cdot> a", thin_tac "x = h \<cdot> a")
apply (frule_tac h = ha in sg_subset_elem[of "H"], assumption+,
       frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       simp add:i_ab)
apply (frule_tac a = a in i_closed, frule_tac a = ha in i_closed,
       simp add:tOp_assocTr41[THEN sym], simp add:tOp_assocTr42,
       simp add:r_i r_unit)
apply (simp add:sg_m_i_closed[of "H"])
done

lemma (in Group) PrSubg4_2:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; x \<in> H \<bullet> (\<rho> a)\<rbrakk> \<Longrightarrow> 
       x \<in> {z. \<exists>v\<in>(H \<bullet> a). \<exists>h\<in>H. h \<cdot> (\<rho> v) = z}"
apply (simp add:rcs_def[of _ "H" "\<rho> a"], erule bexE,
       frule_tac h = h in sg_subset_elem[of "H"], assumption+,
       frule i_closed[of "a"])
apply (frule a_in_rcs[of "H" "a"], assumption, blast)
done

lemma (in Group) rcs_fixed:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; H \<bullet> a = H\<rbrakk>  \<Longrightarrow> a \<in> H"
by (frule a_in_rcs[of "H" "a"], assumption+, simp)

lemma (in Group) rcs_fixed1:"\<lbrakk>G \<guillemotright> H; a \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow>
                                               H \<bullet> a = (H \<bullet> (h \<cdot> a))"
apply (rule rcs_eq1[of "H" "a" "h \<cdot> a"], assumption+)
apply (simp add:rcs_def, blast)
done  

lemma (in Group) rcs_fixed2:"G \<guillemotright> H \<Longrightarrow> \<forall>h\<in>H. H \<bullet> h = H"
apply (rule ballI)
apply (simp add:rcs_Unit2)
done

lemma (in Group) Gp_rcs:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; H \<subseteq> K; x \<in> K\<rbrakk> \<Longrightarrow>
                                   H \<bullet>\<^bsub>(Gp G K)\<^esub> x = (H \<bullet> x)"
by (simp add:rcs_def, simp add:Gp_def)

lemma (in Group) subg_lcs:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; H \<subseteq> K; x \<in> K\<rbrakk> \<Longrightarrow>
                                   x \<diamondsuit>\<^bsub>(Gp G K)\<^esub> H = x \<diamondsuit> H"
by (simp add:lcs_def, simp add:Gp_def)

section "Normal subgroups and Quotient groups"

lemma (in Group) nsg1:"\<lbrakk>G \<guillemotright> H; b \<in> carrier G; h \<in> H;
       \<forall>a\<in> carrier G. \<forall>h\<in>H. (a \<cdot> h)\<cdot> (\<rho> a) \<in> H\<rbrakk> \<Longrightarrow> b \<cdot> h \<cdot> (\<rho> b) \<in> H"
by blast

lemma (in Group) nsg2:"\<lbrakk>G \<guillemotright> H; b \<in> carrier G; h \<in> H;  
       \<forall>a\<in>carrier G. \<forall>h\<in>H. (a \<cdot> h) \<cdot> (\<rho> a) \<in> H\<rbrakk> \<Longrightarrow>  (\<rho> b) \<cdot> h \<cdot> b \<in> H"
apply (frule i_closed[of "b"], 
       frule_tac x = "\<rho> b" in bspec, assumption,
       thin_tac "\<forall>a\<in>carrier G. \<forall>h\<in>H. a \<cdot> h \<cdot> \<rho> a \<in> H",
       frule_tac x = h in bspec, assumption,
       thin_tac "\<forall>h\<in>H. \<rho> b \<cdot> h \<cdot> \<rho> (\<rho> b) \<in> H")
apply (simp add:iop_i_i)
done

lemma (in Group) nsg_subset_elem:"\<lbrakk>G \<triangleright> H; h \<in> H\<rbrakk> \<Longrightarrow> h \<in> carrier G"
by (insert nsg_sg[of "H"], simp add:sg_subset_elem)

lemma (in Group) nsg_l_rcs_eq:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow> a \<diamondsuit> N = N \<bullet> a"
by (simp add: nsg_def)

lemma (in Group) sg_nsg1:"\<lbrakk>G \<guillemotright> H; \<forall>a\<in> carrier G. \<forall>h\<in>H. (a \<cdot> h)\<cdot> (\<rho> a) \<in> H;
                 b \<in> carrier G \<rbrakk> \<Longrightarrow> H \<bullet> b =  b \<diamondsuit> H"
apply (rule equalityI)
 (* H \<bullet> b \<subseteq> b \<diamondsuit> H  *)
  apply (rule subsetI, simp add:rcs_def, erule bexE, frule i_closed[of "b"])
  apply (frule_tac x = "\<rho> b" in bspec, assumption,
         thin_tac "\<forall>a\<in>carrier G. \<forall>h\<in>H. a \<cdot> h \<cdot> \<rho> a \<in> H",
         frule_tac x = h in bspec, assumption,
         thin_tac "\<forall>h\<in>H. \<rho> b \<cdot> h \<cdot> \<rho> (\<rho> b) \<in> H",
         simp add:iop_i_i)
  apply (frule_tac h = h in sg_mult_closedl[of "H" "b"], assumption+, simp,
         frule_tac h = h in sg_subset_elem[of "H"], assumption+,
         simp only:tassoc[of "\<rho> b" _ "b"], thin_tac "h \<cdot> b = x")
  apply (subst lcs_mem_ldiv[of "H" _ "b"], assumption+)

  apply (rule subsetI, simp add:lcs_def, erule bexE)
  apply (frule_tac x = b in bspec, assumption,
         thin_tac "\<forall>a\<in>carrier G. \<forall>h\<in>H. a \<cdot> h \<cdot> \<rho> a \<in> H",
         frule_tac x = h in bspec, assumption,
         thin_tac "\<forall>h\<in>H.  b \<cdot> h \<cdot> (\<rho> b) \<in> H",
         simp add:iop_i_i)
  apply (frule_tac h = h in sg_mult_closedr[of "H" "b"], assumption+, simp)
  apply (subst rcs_eqTr1[of "H" _ "b"], assumption+)
done 

lemma (in Group) cond_nsg:"\<lbrakk>G \<guillemotright> H; \<forall>a\<in>carrier G. \<forall>h\<in>H. a \<cdot> h \<cdot> (\<rho> a) \<in> H \<rbrakk>
                            \<Longrightarrow> G \<triangleright> H" 
apply (subst nsg_def, simp)
apply (rule ballI, rule sg_nsg1, assumption+)
done

lemma (in Group) special_nsg_e:"G \<guillemotright> H \<Longrightarrow> Gp G H \<triangleright> {\<one>}"
apply (simp add:nsg_def,
       frule Group_Gp[of "H"])
apply (rule conjI)
apply (frule Group.special_sg_e[of "\<natural>H"],
       simp add:one_Gp_one[THEN sym])

apply (rule ballI,
       simp add:lcs_def rcs_def, simp add:Gp_def,
       frule_tac h = x in sg_subset_elem[of "H"], assumption+,
       simp add:l_unit r_unit)
done

lemma (in Group) special_nsg_G:"G \<triangleright> (carrier G)" 
apply (simp add:nsg_def,
       simp add:special_sg_G)
apply (rule ballI, rule equalityI)
apply (rule subsetI,
       simp add:rcs_def lcs_def, erule bexE)
apply (frule_tac a = h and b = x in mult_closed, assumption+,
       frule_tac a = x in i_closed,
       frule_tac a1 = x and b1 = "\<rho> x" and c1 = "h \<cdot> x" in tassoc[THEN sym],
                 assumption+, simp add:r_i l_unit,
       frule_tac a = "\<rho> x" and b = xa in mult_closed, assumption+, blast)

apply (rule subsetI, simp add:rcs_def lcs_def, erule bexE,
       frule_tac a = x and b = h in mult_closed, assumption+,
       frule_tac a = x in i_closed,
       frule_tac a = "x \<cdot> h"  and b = "\<rho> x" and c = x in tassoc,
                 assumption+, simp add:l_i r_unit,
       frule_tac a = xa and b = "\<rho> x" in mult_closed, assumption+,
       blast)
done

lemma (in Group) special_nsg_G1:"G \<guillemotright> H \<Longrightarrow> Gp G H \<triangleright> H" 
apply (frule Group_Gp[of "H"], frule Group.special_nsg_G[of "\<natural>H"])
apply (simp add:Gp_carrier)
done

lemma (in Group) nsgTr0:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; b \<in> N \<bullet> a \<rbrakk>
                        \<Longrightarrow>  (a \<cdot> (\<rho> b) \<in> N) \<and> ((\<rho> a) \<cdot> b \<in> N)"
apply (frule nsg_sg[of "N"],
       frule rcs_eqTr1[of "N" "b" "a"], assumption+, simp,
       frule i_closed[of "a"], 
       frule sg_i_closed[of "N" "b \<cdot> \<rho> a"], assumption, simp add:i_ab iop_i_i)
apply (simp add:nsg_l_rcs_eq[THEN sym, of "N" "a"],
       subst lcs_mem_ldiv[THEN sym, of "N" "b" "a"], assumption+)
done

lemma (in Group) nsgTr1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; b \<cdot> (\<rho> a) \<in> N\<rbrakk>
                         \<Longrightarrow> (\<rho> b) \<cdot> a \<in> N"
apply (frule nsg_sg[of "N"],
       simp add:rcs_eqTr1[THEN sym, of "N" "b" "a"],
       simp add:nsg_l_rcs_eq[THEN sym])
apply (simp add:lcs_mem_ldiv[of "N" "b" "a"],
       rule lcs_tool1, assumption+)
done      

lemma (in Group) nsgTr2:"\<lbrakk>a \<in> carrier G; b \<in> carrier G; a1 \<in> carrier G; 
       b1 \<in> carrier G \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> (\<rho> (a1 \<cdot> b1)) = 
                          a \<cdot> (((b \<cdot> (\<rho> b1)) \<cdot> ((\<rho> a1) \<cdot> a)) \<cdot> (\<rho> a))"
apply (frule i_closed[of "a1"], frule i_closed[of "b1"],
       frule i_closed[of "a"],
       frule mult_closed[of "b" "\<rho> b1"], assumption+,
       frule mult_closed[of "\<rho> a1" "a"], assumption+,
       subst tassoc[of "b \<cdot> (\<rho> b1)" "(\<rho> a1) \<cdot> a" "\<rho> a"], assumption+,
       simp add:tassoc[of "\<rho> a1" "a" "\<rho> a"] r_i r_unit) 
apply (simp add:i_ab,
       subst tassoc[of "a" "b" "(\<rho> b1) \<cdot> (\<rho> a1)"], assumption+,
       rule mult_closed, assumption+,
       simp add:tassoc[THEN sym, of "b" "\<rho> b1" "\<rho> a1"])
done

lemma (in Group) nsgPr1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; h \<in> N\<rbrakk> \<Longrightarrow>
                                                 a \<cdot> (h \<cdot> (\<rho> a)) \<in> N"
apply (frule nsg_sg[of "N"], 
       frule sg_subset_elem[of "N" "h"], assumption+,
       frule i_closed[of "a"],
       frule rcs_fixed1[THEN sym, of "N" "\<rho> a" "h"], assumption+, 
       frule mult_closed[of "h" "\<rho> a"], assumption+)
apply (frule a_in_rcs[of "N" "h \<cdot> (\<rho> a)"], assumption+, simp,
       thin_tac "N \<bullet> (h \<cdot> \<rho> a) = N \<bullet> \<rho> a")
apply (simp add:nsg_l_rcs_eq[THEN sym, of "N" "\<rho> a"],
       simp add:lcs_mem_ldiv[of "N" "h \<cdot> (\<rho> a)" "\<rho> a"] iop_i_i)
done       
    
lemma (in Group) nsgPr1_1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G ; h \<in> N\<rbrakk> \<Longrightarrow> 
                              (a \<cdot> h) \<cdot> (\<rho> a) \<in> N"
apply (frule nsgPr1[of "N" "a" "h"], assumption+)
apply (frule nsg_sg[of "N"],
       frule sg_subset_elem[of "N" "h"], assumption+,
       frule i_closed[of "a"],
       simp add:tassoc[THEN sym, of "a" "h" "\<rho> a"])
done

lemma (in Group) nsgPr2:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; h \<in> N\<rbrakk> \<Longrightarrow>
                                   (\<rho> a) \<cdot> (h \<cdot> a) \<in> N"
apply (frule i_closed[of "a"],
       frule nsgPr1[of "N" "\<rho> a" "h"], assumption+)
apply (simp add:iop_i_i)
done

lemma (in Group) nsgPr2_1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; h \<in> N\<rbrakk> \<Longrightarrow>
                                              (\<rho> a) \<cdot> h \<cdot> a \<in> N"
apply (frule i_closed[of "a"],
       frule  nsgPr1_1[of "N" "\<rho> a" "h"], assumption+, simp add:iop_i_i)
done

lemma (in Group) nsgTr3:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; 
a1 \<in> carrier G; b1 \<in> carrier G;  a \<cdot> (\<rho> a1) \<in> N; b \<cdot> (\<rho> b1) \<in> N\<rbrakk> \<Longrightarrow> 
                  (a \<cdot> b) \<cdot> (\<rho> (a1 \<cdot> b1)) \<in> N"
apply (frule nsg_sg[of "N"]) 
apply (frule  nsgTr2 [of "a" "b" "a1" "b1"], assumption+)
apply (frule  nsgTr1 [of "N" "a1" "a"], assumption+)

apply (frule i_closed[of "a"],
       frule sg_i_closed [of "N" "(\<rho> a) \<cdot> a1"], assumption+, 
        simp add:i_ab[of "\<rho> a" "a1"] iop_i_i,
       frule sg_mult_closed[of "N" "b \<cdot> (\<rho> b1)" "(\<rho> a1) \<cdot> a"], assumption+)
apply (rule nsgPr1[of "N" "a" "b \<cdot> (\<rho> b1) \<cdot> ((\<rho> a1) \<cdot> a)"], assumption+)
done

lemma (in Group) nsg_in_Gp:"\<lbrakk>G \<triangleright> N; G \<guillemotright> H; N \<subseteq> H\<rbrakk> \<Longrightarrow> (Gp G H) \<triangleright> N"
apply (frule Group_Gp [of "H"],
       frule nsg_sg[of "N"]) 
apply (rule Group.cond_nsg [of "\<natural>H" "N"], assumption+,
       simp add:sg_sg[of "H" "N"])
apply (rule ballI, rule ballI,
       (subst Gp_def)+, simp add:Gp_carrier)
apply (frule_tac h = a in sg_subset_elem[of "H"], assumption+,
       rule_tac a = a and h = h in nsgPr1_1[of "N"], assumption+)
done

lemma (in Group) nsgTr4:"\<lbrakk>G \<triangleright> N; a \<in> carrier G;  x \<in> N \<bullet> a\<rbrakk> \<Longrightarrow> 
                            (\<rho> x) \<in> N \<bullet> (\<rho> a)"
apply (frule nsgTr0 [of "N"], assumption+)
apply (frule nsg_sg[of "N"], rule a_in_rcs[of "N"], assumption+,
       thin_tac "a \<cdot> \<rho> a \<in> N \<and> \<rho> a \<cdot> a \<in> N",
       frule nsg_sg[of "N"],
       frule rcs_subset_elem[of "N" "a" "x"], assumption+,
       simp add:rcs_eqTr1[of "N" "x" "a"])
apply (frule nsgTr1[of "N" "a" "x"], assumption+,
       frule i_closed[of "x"],
       subst rcs_eqTr1[of "N" "\<rho> x" "\<rho> a"], assumption+,
       simp add:i_closed, simp add:iop_i_i)
done

lemma (in Group) c_topTr1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; 
       a1 \<in> carrier G; b1 \<in> carrier G; N \<bullet> a = N \<bullet> a1; N \<bullet> b = N \<bullet> b1\<rbrakk> \<Longrightarrow> 
                      N \<bullet> (a \<cdot> b) = N \<bullet> (a1 \<cdot> b1)"
apply (frule nsg_sg[of "N"],
       frule mult_closed[of "a" "b"], assumption+,
       frule mult_closed[of "a1" "b1"], assumption+,
       simp add:rcs_eq[THEN sym, of "N" "a" "a1"],
       simp add:rcs_eq[THEN sym, of "N" "b" "b1"])
apply (subst rcs_eq[THEN sym, of "N" "a \<cdot> b" "a1 \<cdot> b1"], assumption+)
apply (rule nsgTr3[of "N" "a1" "b1" "a" "b"], assumption+)
done

lemma (in Group) c_topTr2:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; a1 \<in> carrier G;
                 N \<bullet> a = N \<bullet> a1 \<rbrakk> \<Longrightarrow> N \<bullet> (\<rho> a) = N \<bullet> (\<rho> a1)"
apply (frule nsg_sg[of "N"], 
       simp add:rcs_eq[THEN sym, of "N" "a" "a1"])
apply (subst rcs_eq[THEN sym, of "N" "\<rho> a" "\<rho> a1"], assumption+,
       simp add:i_closed, simp add:i_closed, simp add:iop_i_i)
apply (rule nsgTr1[of "N" "a" "a1"], assumption+)
done

lemma (in Group) c_iop_welldefTr1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                         c_iop G N (N \<bullet> a) \<subseteq>  N \<bullet> (\<rho> a)"
apply (frule nsg_sg[of "N"],
       frule i_closed[of "a"])  
apply (rule subsetI)
apply (simp add:c_iop_def rcs_in_set_rcs)
apply (erule bexE)+
apply (simp add:rcs_def[of _ "N" "a"], erule bexE,
       rotate_tac -1, frule sym, thin_tac "ha \<cdot> a = xa", simp,
       thin_tac "xa = ha \<cdot> a")
apply (frule_tac h = ha in sg_subset_elem[of "N"], assumption+,
       frule_tac a = ha and b = a in mult_closed, assumption+,
       frule_tac a = "ha \<cdot> a" in i_closed,
       frule_tac h = h in sg_subset_elem[of "N"], assumption+,
       frule_tac a = h and b = "\<rho> (ha \<cdot> a)" in mult_closed, assumption+)
apply (frule_tac a = "h \<cdot> \<rho> (ha \<cdot> a)" and b = x in r_mult_eqn[of _ _ 
       "a \<cdot> (\<rho> a)"], simp, simp add:r_i unit_closed, assumption)
apply (frule_tac a = "h \<cdot> \<rho> (ha \<cdot> a)" in tassoc[of _ "a" "\<rho> a"], assumption+,
       frule_tac a = "h \<cdot> \<rho> (ha \<cdot> a)" and A = "carrier G" and b = x in 
                 eq_elem_in, assumption+,
       thin_tac "h \<cdot> \<rho> (ha \<cdot> a) = x", simp,
       thin_tac "h \<cdot> \<rho> (ha \<cdot> a) \<cdot> (a \<cdot> \<rho> a) = x \<cdot> (a \<cdot> \<rho> a)")
apply (frule_tac a = h and b = "\<rho> (ha \<cdot> a)" and c = a in tassoc, assumption+,
       simp, thin_tac "h \<cdot> \<rho> (ha \<cdot> a) \<cdot> a = h \<cdot> (\<rho> (ha \<cdot> a) \<cdot> a)")
apply (simp add:i_ab r_i r_unit)
apply (frule_tac x = ha in sg_i_closed[of "N"], assumption+,
       frule sym, thin_tac "h \<cdot> (\<rho> a \<cdot> \<rho> ha \<cdot> a) \<cdot> \<rho> a = x", simp,
       thin_tac "x = h \<cdot> (\<rho> a \<cdot> \<rho> ha \<cdot> a) \<cdot> \<rho> a")
apply (frule_tac h = "\<rho> ha" in nsgPr2_1[of "N" "a"], assumption+,
       frule_tac x = h and y = "\<rho> a \<cdot> \<rho> ha \<cdot> a" in sg_mult_closed, assumption+)
apply (simp add:rcs_def, blast)
done

lemma (in Group) c_iop_welldefTr2:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                                   N \<bullet> (\<rho> a) \<subseteq>  c_iop G N (N \<bullet> a)"
apply (rule subsetI) 
 apply (frule nsg_sg[of "N"],
        frule i_closed[of "a"],
        frule_tac x = x in rcs_subset_elem[of "N" "\<rho> a"], assumption+)
apply (simp add:c_iop_def,
       simp add:rcs_in_set_rcs[of "N" "a"],
       simp add:rcs_def[of _ "N" "\<rho> a"])
 apply (frule a_in_rcs[of "N" "a"], assumption, blast)
done
 
lemma (in Group) c_iop_welldef:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                 c_iop G N (N \<bullet> a) =  N \<bullet> (\<rho> a)"  
 apply (rule equalityI) 
 apply (simp only:c_iop_welldefTr1[of "N" "a"])
 apply (simp only:c_iop_welldefTr2[of "N" "a"])
done

lemma (in Group) c_top_welldefTr1:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; 
          b \<in> carrier G; x \<in> N \<bullet> a; y \<in> N \<bullet> b\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> N \<bullet> (a \<cdot> b)"
apply (frule nsg_sg[of "N"])
apply (frule_tac x = x in rcs_subset_elem[of "N" "a"], assumption+,
       frule_tac x = y in rcs_subset_elem[of "N" "b"], assumption+,
       frule rcs_eqTr1[of "N" "x" "a"], assumption+,
       frule rcs_eqTr1[of "N" "y" "b"], assumption+, simp)      
apply (frule_tac mult_closed[of "a" "b"], assumption+,
       frule_tac mult_closed[of "x" "y"], assumption+)
apply (subst rcs_eqTr1[of "N" "x \<cdot> y" "a \<cdot> b"], assumption+,
       rule nsgTr3[of "N" "x" "y" "a" "b"], assumption+)
done

lemma (in Group) c_top_welldefTr2:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G \<rbrakk> 
                       \<Longrightarrow> c_top G N (N \<bullet> a) (N \<bullet> b) \<subseteq>  N \<bullet> (a \<cdot> b)"
apply (frule nsg_sg[of "N"],
       simp add:c_top_def, simp add:rcs_in_set_rcs)
apply (rule subsetI, simp, (erule bexE)+,
       frule_tac x = xa and y = y in c_top_welldefTr1[of "N" "a" "b"], 
       assumption+, simp)
done

lemma (in Group) c_top_welldefTr4:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; 
      x \<in> N \<bullet> (a \<cdot> b)\<rbrakk> \<Longrightarrow> x \<in> c_top G N (N \<bullet> a) (N \<bullet> b)" 
apply (frule nsg_sg[of "N"]) 
apply (simp add:c_top_def, simp add:rcs_in_set_rcs,
       simp add:rcs_def[of _ "N" "a \<cdot> b"], erule bexE,
       frule_tac h = h in sg_subset_elem[of "N"], assumption+,
       simp add:tassoc[THEN sym, of _ "a" "b"])
apply (frule a_in_rcs[of "N" "b"], assumption,
       frule_tac h1 = h in rcs_fixed1[THEN sym, of "N" "a"], assumption+,
       frule_tac a = h and b = a in mult_closed, assumption+,
       frule_tac a = "h \<cdot> a" in a_in_rcs[of "N"], assumption+, simp)
apply blast
done

lemma (in Group) c_top_welldefTr5:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
                             N \<bullet> (a \<cdot> b) \<subseteq> c_top G N (N \<bullet> a) (N \<bullet> b)"
by (rule subsetI,
       rule c_top_welldefTr4[of "N" "a" "b" _], assumption+)

lemma (in Group) c_top_welldef:"\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
                 N \<bullet> (a \<cdot> b) = c_top G N (N \<bullet> a) (N \<bullet> b)"
by (rule equalityI, simp only:c_top_welldefTr5, simp only:c_top_welldefTr2)

lemma (in Group) Qg_unitTr:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                            c_top G N N (N \<bullet> a) = N \<bullet> a" 
apply (frule nsg_sg[of "N"])
apply (rule equalityI)
 apply (rule subsetI, simp add:c_top_def) 
 apply (simp add:unit_rcs_in_set_rcs rcs_in_set_rcs)
 apply (erule bexE)+
 apply (simp add:rcs_def, erule bexE)
 apply (frule sym, thin_tac "xa \<cdot> y = x", frule sym, thin_tac "h \<cdot> a = y",
        simp, thin_tac "x = xa \<cdot> (h \<cdot> a)", thin_tac "y = h \<cdot> a",
       frule_tac h = xa in sg_subset_elem[of "N"], assumption+,
       frule_tac h = h in sg_subset_elem[of "N"], assumption+,
       simp add:tassoc[THEN sym],
       frule_tac x = xa and y = h in  sg_mult_closed[of "N"], assumption+,
       blast)
apply (rule subsetI,
       simp add:c_top_def, simp add:unit_rcs_in_set_rcs rcs_in_set_rcs)
apply (frule_tac x = x in mem_rcs [of "N" _ "a"], assumption, erule bexE,
       frule a_in_rcs[of "N" "a"], assumption, blast)
done                    

lemma (in Group) Qg_unit:"G \<triangleright> N  \<Longrightarrow> \<forall>x\<in>set_rcs G N. c_top G N N x = x" 
by (rule ballI,
       simp add:set_rcs_def, erule bexE, simp,
       simp add:Qg_unitTr)

lemma (in Group) Qg_iTr:"\<lbrakk>G \<triangleright> N; a \<in> carrier G\<rbrakk> \<Longrightarrow>
                         c_top G N (c_iop G N (N \<bullet> a)) (N \<bullet> a) = N"
apply (simp add:c_iop_welldef [of "N" "a"])
apply (frule i_closed[of "a"],
       simp add:c_top_welldef[THEN sym, of "N" "\<rho> a" "a"],
       simp add:l_i)
apply (frule nsg_sg[of "N"],
       simp add:rcs_Unit1[of "N"])
done  

lemma (in Group) Qg_i:"G \<triangleright> N  \<Longrightarrow>
                         \<forall>x \<in> set_rcs G N. c_top G N (c_iop G N x) x = N"
apply (rule ballI, simp add:set_rcs_def, erule bexE)
apply (simp add:Qg_iTr)
done

lemma (in Group) Qg_tassocTr:
  "\<lbrakk>G \<triangleright> N; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> 
   c_top G N (N \<bullet> a) (c_top G N (N \<bullet> b) (N \<bullet> c)) = 
                           c_top G N (c_top G N (N \<bullet> a) (N \<bullet> b)) (N \<bullet> c)"
apply (frule mult_closed[of "b" "c"], assumption+,
       frule mult_closed[of "a" "b"], assumption+,
       simp add:c_top_welldef[THEN sym])
apply (simp add:tassoc)
done

lemma (in Group) Qg_tassoc: "G \<triangleright> N \<Longrightarrow>
\<forall>X\<in>set_rcs G N. \<forall>Y\<in>set_rcs G N. \<forall>Z\<in>set_rcs G N. c_top G N X (c_top G N Y Z) 
                                   = c_top G N (c_top G N X Y) Z"
apply (rule ballI)+ apply (simp add:set_rcs_def, (erule bexE)+)
apply (simp add:Qg_tassocTr)
done

lemma (in Group) Qg_top:"G \<triangleright> N \<Longrightarrow> 
                 c_top G N : set_rcs G N \<rightarrow> set_rcs G N \<rightarrow> set_rcs G N"
apply (rule Pi_I, rule Pi_I, simp add:set_rcs_def, (erule bexE)+,
       simp add:c_top_welldef[THEN sym])
 apply (metis mult_closed)
done

lemma (in Group) Qg_top_closed:"\<lbrakk>G \<triangleright> N; A \<in> set_rcs G N; B \<in> set_rcs G N\<rbrakk> \<Longrightarrow>
                                   c_top G N A B \<in> set_rcs G N"
apply (frule Qg_top[of "N"])
apply (frule funcset_mem [of "c_top G N" "set_rcs G N" _ "A"], assumption)
apply (rule funcset_mem[of "c_top G N A" "set_rcs G N" "set_rcs G N" "B"],
           assumption, assumption)
done

lemma (in Group) Qg_iop: "G \<triangleright> N \<Longrightarrow>
               c_iop G N :set_rcs G N \<rightarrow> set_rcs G N"
apply (rule Pi_I)
 apply (simp add:set_rcs_def, erule bexE)
 apply (simp add:c_iop_welldef)
apply (frule_tac a = a in i_closed, blast)
done

lemma (in Group) Qg_iop_closed:"\<lbrakk>G \<triangleright> N; A \<in> set_rcs G N\<rbrakk> \<Longrightarrow>
                                   c_iop G N A \<in> set_rcs G N"
by (frule Qg_iop[of "N"],
       erule funcset_mem, assumption)

lemma (in Group) Qg_unit_closed: "G \<triangleright> N \<Longrightarrow>  N \<in> set_rcs G N"
by (frule nsg_sg[of "N"],
       simp only:unit_rcs_in_set_rcs)

theorem (in Group) Group_Qg:"G \<triangleright> N \<Longrightarrow>  Group (Qg G N)" 
apply (frule Qg_top [of "N"], frule Qg_iop [of "N"],
       frule Qg_unit[of "N"], frule Qg_i[of "N" ],
       frule Qg_tassoc[of "N"], frule Qg_unit_closed[of "N" ])
apply (simp add:Qg_def Group_def)
done

lemma (in Group) Qg_one:"G \<triangleright> N \<Longrightarrow> one (G / N) = N"
by (simp add:Qg_def)

lemma (in Group) Qg_carrier:"carrier (G / (N::'a set)) = set_rcs G N" 
by (simp add:Qg_def) (** only a trick *)

lemma (in Group) Qg_unit_group:"G \<triangleright> N \<Longrightarrow> 
                        (set_rcs G N = {N}) = (carrier G = N)"
apply (rule iffI)
 apply (rule contrapos_pp, simp+,
       frule nsg_sg[of "N"],
       frule sg_subset[of "N"],
       frule sets_not_eq[of "carrier G" "N"], assumption, erule bexE,
       frule_tac a = a in rcs_in_set_rcs[of "N"], assumption+,
       simp)  
 apply (frule_tac a = a in a_in_rcs[of "N"], assumption+,
        simp)
apply (simp add:set_rcs_def, frule nsg_sg[of "N"],
       frule rcs_fixed2[of "N"], frule_tac sg_unit_closed[of "N"], blast)
done

lemma (in Group) Gp_Qg:"G \<triangleright> N \<Longrightarrow> Gp(G / N) (carrier(G / N)) = G / N"
by (simp add:Gp_def Qg_def)

lemma (in Group) Pj_hom0:"\<lbrakk>G \<triangleright> N; x \<in> carrier G; y \<in> carrier G\<rbrakk>
                 \<Longrightarrow> Pj G N (x \<cdot> y) = (Pj G N x) \<cdot>\<^bsub>(G / N)\<^esub> (Pj G N y)"
apply (simp add:Pj_def mult_closed)
apply (simp add:Qg_def, simp add:c_top_welldef)
done

lemma (in Group) Pj_ghom:"G \<triangleright> N \<Longrightarrow> (Pj G N) \<in> gHom G (G / N)"
apply (simp add:gHom_def)
apply (rule conjI,
       simp add:restrict_def Pj_def extensional_def)
apply (rule conjI, simp add:Pi_def,
       rule allI, rule impI,
       simp add:Qg_def set_rcs_def, simp add:Pj_def, blast)
apply ((rule ballI)+, simp add:Pj_hom0)
done

lemma (in Group) Pj_mem:"\<lbrakk>G \<triangleright> N; x \<in> carrier G\<rbrakk> \<Longrightarrow> (Pj G N) x = N \<bullet> x"
by (simp add:Pj_def)

lemma (in Group) Pj_gsurjec:"G \<triangleright> N \<Longrightarrow> gsurjec G (G/N) (Pj G N)"
apply (simp add:gsurjec_def)
apply (simp add:Pj_ghom) 
apply (rule surj_to_test[of "Pj G N" "carrier G" "carrier (G / N)"],
       frule Pj_ghom[of "N"], simp add:gHom_def,
       rule ballI,
       simp add:Qg_def set_rcs_def, erule bexE)
 apply (frule_tac x = a in Pj_mem[of "N"], assumption, simp, blast)
done

lemma (in Group) lcs_in_Gp:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; K \<subseteq> H; a \<in> H\<rbrakk>  \<Longrightarrow> 
                                       a \<diamondsuit> K = a \<diamondsuit>\<^bsub>(Gp G H)\<^esub> K"
by (simp add:lcs_def, simp add:Gp_def)

lemma (in Group) rcs_in_Gp:"\<lbrakk>G \<guillemotright> H; G \<guillemotright> K; K \<subseteq> H; a \<in> H \<rbrakk>  \<Longrightarrow>
                              K \<bullet> a = K \<bullet>\<^bsub>(Gp G H)\<^esub> a"
apply (simp add:rcs_def)
apply (simp add:Gp_def)
done

end
