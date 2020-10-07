(**       Algebra4
                            author Hidetsune Kobayashi
                                   Lingjun Chen (part of Chap 4. section 2,
                                   with revision by H. Kobayashi)
                             Group You Santo
                             Department of Mathematics
                             Nihon University
                             h_coba@math.cst.nihon-u.ac.jp
                             May 3, 2004.
                             April 6, 2007 (revised)

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem (continued)
     section 20.   abelian groups
     subsection 20-1. Homomorphism of abelian groups
     subsection 20-2  quotient abelian group
   section 21  direct product and direct sum of abelian groups,
               in general case

 chapter 4.  Ring theory
   section 1.  Definition of a ring and an ideal
   section 2.  Calculation of elements
   section 3.  ring homomorphisms
   section 4.  quotient rings
   section 5.  primary ideals, prime ideals
 **)

theory Algebra4
imports Algebra3
begin

section "Abelian groups"

record 'a aGroup = "'a carrier" +
  pop      :: "['a, 'a ] \<Rightarrow> 'a"  (infixl "\<plusminus>\<index>" 62)
  mop      :: "'a  \<Rightarrow> 'a"        ("(-\<^sub>a\<index> _)" [64]63 )
  zero     :: "'a"               ("\<zero>\<index>")

locale aGroup =
  fixes A (structure)
 assumes
         pop_closed: "pop A \<in> carrier A \<rightarrow> carrier A \<rightarrow> carrier A"
 and     aassoc : "\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A\<rbrakk> \<Longrightarrow>
         (a \<plusminus> b) \<plusminus> c = a \<plusminus> (b \<plusminus> c)"
 and     pop_commute:"\<lbrakk>a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow> a \<plusminus> b = b \<plusminus> a"
 and     mop_closed:"mop A \<in> carrier A \<rightarrow> carrier A"
 and     l_m :"a \<in> carrier A \<Longrightarrow>  (-\<^sub>a a) \<plusminus> a = \<zero>"
 and     ex_zero: "\<zero> \<in> carrier A"
 and     l_zero:"a \<in> carrier A \<Longrightarrow> \<zero> \<plusminus> a = a"

definition
  b_ag :: "_  \<Rightarrow>
   \<lparr>carrier:: 'a set, top:: ['a, 'a] \<Rightarrow> 'a , iop:: 'a \<Rightarrow> 'a, one:: 'a \<rparr>" where
  "b_ag A = \<lparr>carrier = carrier A, top = pop A, iop = mop A, one = zero A \<rparr>"

definition
  asubGroup :: "[_ , 'a set] \<Rightarrow> bool" where
  "asubGroup A H \<longleftrightarrow> (b_ag A) \<guillemotright> H"

definition
  aqgrp :: "[_ , 'a set] \<Rightarrow>
         \<lparr> carrier::'a set set, pop::['a  set, 'a set] \<Rightarrow> 'a set,
           mop::'a set \<Rightarrow> 'a set, zero :: 'a set \<rparr>" where
  "aqgrp A H = \<lparr>carrier = set_rcs (b_ag A) H,
         pop = \<lambda>X. \<lambda>Y. (c_top (b_ag A) H X Y),
         mop = \<lambda>X. (c_iop (b_ag A) H X), zero = H \<rparr>"

definition
  ag_idmap :: "_ \<Rightarrow> ('a \<Rightarrow> 'a)"  ("(aI\<^bsub>_\<^esub>)") where
  "aI\<^bsub>A\<^esub> = (\<lambda>x\<in>carrier A. x)"

abbreviation
  ASubG :: "[('a, 'more) aGroup_scheme, 'a set] => bool"   (infixl "+>" 58) where
  "A +> H == asubGroup A H"

definition
  Ag_ind :: "[_ , 'a \<Rightarrow> 'd] \<Rightarrow> 'd aGroup" where
  "Ag_ind A f = \<lparr>carrier = f`(carrier A),
    pop = \<lambda>x \<in> f`(carrier A). \<lambda>y \<in> f`(carrier A).
               f(((invfun (carrier A) (f`(carrier A)) f) x) \<plusminus>\<^bsub>A\<^esub>
                    ((invfun (carrier A) (f`(carrier A)) f) y)),
    mop = \<lambda>x\<in>(f`(carrier A)). f (-\<^sub>a\<^bsub>A\<^esub> ((invfun (carrier A) (f`(carrier A)) f) x)),
    zero = f (\<zero>\<^bsub>A\<^esub>)\<rparr>"

definition
  Agii :: "[_ , 'a \<Rightarrow> 'd] \<Rightarrow> ('a \<Rightarrow> 'd)" where
  "Agii A f = (\<lambda>x\<in>carrier A. f x)"   (** Ag_induced_isomorphism **)

lemma (in aGroup) ag_carrier_carrier:"carrier (b_ag A) = carrier A"
by (simp add:b_ag_def)

lemma (in aGroup) ag_pOp_closed:"\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow>
                                     pop A x y \<in> carrier A"
apply (cut_tac pop_closed)
apply (frule funcset_mem[of "(\<plusminus>) " "carrier A" "carrier A \<rightarrow> carrier A" "x"],
        assumption+)
apply (rule funcset_mem[of "(\<plusminus>) x" "carrier A" "carrier A" "y"], assumption+)
done

lemma (in aGroup) ag_mOp_closed:"x \<in> carrier A \<Longrightarrow> (-\<^sub>a x)  \<in> carrier A"
apply (cut_tac mop_closed)
apply (rule funcset_mem[of "mop A" "carrier A" "carrier A" "x"], assumption+)
done

lemma (in aGroup) asubg_subset:"A +> H \<Longrightarrow> H \<subseteq> carrier A"
apply (simp add:asubGroup_def)
apply (simp add:sg_def, (erule conjE)+)
apply (simp add:ag_carrier_carrier)
done

lemma (in aGroup) ag_pOp_commute:"\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk>  \<Longrightarrow>
           pop A x y = pop A y x"
by (simp add:pop_commute)

lemma (in aGroup) b_ag_group:"Group (b_ag A)"
apply (unfold Group_def)
 apply (simp add:b_ag_def)
apply (simp add:pop_closed mop_closed ex_zero)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:aassoc)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (simp add:l_m)

 apply (rule allI, rule impI)
 apply (simp add:l_zero)
done

lemma (in aGroup) agop_gop:"top (b_ag A) = pop A" (*agpop_gtop*)
 apply (simp add:b_ag_def)
done

lemma (in aGroup) agiop_giop:"iop (b_ag A) = mop A" (*agmop_giop*)
apply (simp add:b_ag_def)
done

lemma (in aGroup) agunit_gone:"one (b_ag A) = \<zero>"
apply (simp add:b_ag_def)
done

lemma (in aGroup) ag_pOp_add_r:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;
                 a = b\<rbrakk>  \<Longrightarrow> a \<plusminus> c =  b \<plusminus> c"
apply simp
done

lemma (in aGroup) ag_add_commute:"\<lbrakk>a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow>
                                                  a \<plusminus> b = b \<plusminus> a"
by (simp add:pop_commute)

lemma (in aGroup) ag_pOp_add_l:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;
                 a = b\<rbrakk>  \<Longrightarrow> c \<plusminus> a =  c \<plusminus> b"
apply simp
done

lemma (in aGroup) asubg_pOp_closed:"\<lbrakk>asubGroup A H; x \<in> H; y \<in> H\<rbrakk>
                                   \<Longrightarrow> pop A x y \<in> H"
apply (simp add:asubGroup_def)
 apply (cut_tac b_ag_group)
 apply (frule Group.sg_mult_closed [of "b_ag A" "H" "x" "y"], assumption+)
apply (simp only:agop_gop)
done

lemma (in aGroup) asubg_mOp_closed:"\<lbrakk>asubGroup A H; x \<in> H\<rbrakk> \<Longrightarrow> -\<^sub>a x \<in> H"
apply (simp add:asubGroup_def)
apply (cut_tac b_ag_group)
apply (frule Group.sg_i_closed[of "b_ag A" "H" "x"], assumption+)
apply (simp add:agiop_giop)
done

lemma (in aGroup) asubg_subset1:"\<lbrakk>asubGroup A H; x \<in> H\<rbrakk> \<Longrightarrow> x \<in> carrier A"
apply (simp add:asubGroup_def)
apply (cut_tac b_ag_group)
apply (frule Group.sg_subset_elem[of "b_ag A" "H" "x"], assumption+)
apply (simp add:ag_carrier_carrier)
done

lemma (in aGroup) asubg_inc_zero:"asubGroup A H \<Longrightarrow> \<zero> \<in> H"
apply (simp add:asubGroup_def)
apply (cut_tac b_ag_group)
apply (frule Group.sg_unit_closed[of "b_ag A" "H"], assumption)
apply (simp add:b_ag_def)
done

lemma (in aGroup) ag_inc_zero:"\<zero> \<in> carrier A"
by (simp add:ex_zero)

lemma (in aGroup) ag_l_zero:"x \<in> carrier A \<Longrightarrow> \<zero> \<plusminus> x = x"
by (simp add:l_zero)

lemma (in aGroup) ag_r_zero:"x \<in> carrier A \<Longrightarrow> x \<plusminus> \<zero> = x"
apply (cut_tac ex_zero)
apply (subst pop_commute, assumption+)
apply (rule ag_l_zero, assumption)
done

lemma (in aGroup) ag_l_inv1:"x \<in> carrier A \<Longrightarrow> (-\<^sub>a x) \<plusminus> x = \<zero>"
by (simp add:l_m)

lemma (in aGroup) ag_r_inv1:"x \<in> carrier A \<Longrightarrow> x \<plusminus> (-\<^sub>a x) = \<zero>"
by (frule ag_mOp_closed[of "x"],
       subst ag_pOp_commute, assumption+,
       simp add:ag_l_inv1)

lemma (in aGroup) ag_pOp_assoc:"\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk>
                \<Longrightarrow> (x \<plusminus> y) \<plusminus> z = x \<plusminus> (y \<plusminus> z)"
by (simp add:aassoc)

lemma (in aGroup) ag_inv_unique:"\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<plusminus> y = \<zero>\<rbrakk> \<Longrightarrow>
                                     y = -\<^sub>a x"
apply (frule ag_mOp_closed[of "x"],
       frule aassoc[of "-\<^sub>a x" "x" "y"], assumption+,
       simp add:l_m l_zero ag_r_zero)
done

lemma (in aGroup) ag_inv_inj:"\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<noteq> y\<rbrakk> \<Longrightarrow>
                                          (-\<^sub>a x) \<noteq> (-\<^sub>a y)"
apply (rule contrapos_pp, simp+)
apply (frule ag_mOp_closed[of "y"],
       frule aassoc[of "y" "-\<^sub>a y" "x"], assumption+)
apply (simp only:ag_r_inv1,
       frule sym, thin_tac "-\<^sub>a x = -\<^sub>a y", simp add:l_m)
apply (simp add:l_zero ag_r_zero)
done

lemma (in aGroup) pOp_assocTr41:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;
 d \<in> carrier A\<rbrakk> \<Longrightarrow> a \<plusminus> b \<plusminus> c \<plusminus> d = a \<plusminus> b \<plusminus> (c \<plusminus> d)"
by (frule ag_pOp_closed[of "a" "b"], assumption+,
    rule aassoc[of "a \<plusminus> b" "c" "d"], assumption+)

lemma (in aGroup) pOp_assocTr42:"\<lbrakk>a \<in> carrier A; b \<in> carrier A;
 c \<in> carrier A; d \<in> carrier A\<rbrakk> \<Longrightarrow> a \<plusminus> b \<plusminus> c \<plusminus> d = a \<plusminus> (b \<plusminus> c) \<plusminus> d"
by (simp add:aassoc[THEN sym, of "a" "b" "c"])

lemma (in aGroup) pOp_assocTr43:"\<lbrakk>a \<in> carrier A; b \<in> carrier A;
 c \<in> carrier A; d \<in> carrier A\<rbrakk> \<Longrightarrow> a \<plusminus> b \<plusminus> (c \<plusminus> d) = a \<plusminus> (b \<plusminus> c) \<plusminus> d"
by (subst  pOp_assocTr41[THEN sym], assumption+,
       rule pOp_assocTr42, assumption+)

lemma (in aGroup) pOp_assoc_cancel:"\<lbrakk>a \<in> carrier A; b \<in> carrier A;
 c \<in> carrier A\<rbrakk> \<Longrightarrow> a \<plusminus> -\<^sub>a b \<plusminus> (b \<plusminus> -\<^sub>a c) = a \<plusminus> -\<^sub>a c"
apply (subst pOp_assocTr43, assumption)
apply (simp add:ag_l_inv1 ag_mOp_closed)+
apply (simp add:ag_r_zero)
done

lemma (in aGroup) ag_p_inv:"\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow>
                                     (-\<^sub>a (x \<plusminus> y)) = (-\<^sub>a x) \<plusminus> (-\<^sub>a y)"
apply (frule ag_mOp_closed[of "x"], frule ag_mOp_closed[of "y"],
       frule ag_pOp_closed[of "x" "y"], assumption+)
apply (frule aassoc[of "x \<plusminus> y" "-\<^sub>a x" "-\<^sub>a y"], assumption+,
       simp add:pOp_assocTr43, simp add:pop_commute[of "y" "-\<^sub>a x"],
       simp add:aassoc[THEN sym, of "x" "-\<^sub>a x" "y"],
       simp add:ag_r_inv1 l_zero)
apply (frule ag_pOp_closed[of "-\<^sub>a x" "-\<^sub>a y"], assumption+,
       simp add:pOp_assocTr41,
       rule ag_inv_unique[THEN sym, of "x \<plusminus> y" "-\<^sub>a x \<plusminus> -\<^sub>a y"], assumption+)
done

lemma (in aGroup) gEQAddcross: "\<lbrakk>l1 \<in> carrier A; l2 \<in> carrier A;
      r1 \<in> carrier A; r1 \<in> carrier A; l1 = r2; l2 = r1\<rbrakk> \<Longrightarrow>
                          l1 \<plusminus> l2 = r1 \<plusminus> r2"
  apply (simp add:ag_pOp_commute)
  done

lemma (in aGroup) ag_eq_sol1:"\<lbrakk>a \<in> carrier A; x\<in> carrier A; b\<in> carrier A;
                               a \<plusminus> x = b\<rbrakk> \<Longrightarrow> x = (-\<^sub>a a) \<plusminus> b"
apply (frule ag_mOp_closed[of "a"])
apply (frule aassoc[of "-\<^sub>a a" "a" "x"], assumption+)
apply (simp add:l_m l_zero)
done

lemma (in aGroup) ag_eq_sol2:"\<lbrakk>a \<in> carrier A; x\<in> carrier A; b\<in> carrier A;
                                x \<plusminus> a = b\<rbrakk> \<Longrightarrow> x = b \<plusminus> (-\<^sub>a a)"
apply (frule ag_mOp_closed[of "a"],
       frule aassoc[of "x" "a" "-\<^sub>a a"], assumption+,
       simp add:ag_r_inv1 ag_r_zero)
done

lemma (in aGroup) ag_add4_rel:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;
 d \<in> carrier A \<rbrakk> \<Longrightarrow> a \<plusminus> b \<plusminus> (c \<plusminus> d) =  a \<plusminus> c \<plusminus> (b \<plusminus> d)"
apply (simp add:pOp_assocTr43[of "a" "b" "c" "d"],
       simp add:ag_pOp_commute[of "b" "c"],
       simp add:pOp_assocTr43[THEN sym, of "a" "c" "b" "d"])
done

lemma (in aGroup) ag_inv_inv:"x \<in> carrier A \<Longrightarrow> -\<^sub>a (-\<^sub>a x) = x"
by (frule ag_l_inv1[of "x"], frule ag_mOp_closed[of "x"],
       rule  ag_inv_unique[THEN sym, of "-\<^sub>a x" "x"], assumption+)

lemma (in aGroup) ag_inv_zero:"-\<^sub>a \<zero> = \<zero>"
apply (cut_tac ex_zero)
apply (frule l_zero[of "\<zero>"])
apply (rule ag_inv_unique[THEN sym], assumption+)
done

lemma (in aGroup) ag_diff_minus:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;
                   a \<plusminus> (-\<^sub>a b) = c\<rbrakk> \<Longrightarrow> b \<plusminus> (-\<^sub>a a) = (-\<^sub>a c)"
apply (frule sym, thin_tac "a \<plusminus> -\<^sub>a b = c", simp, thin_tac "c = a \<plusminus> -\<^sub>a b")
apply (frule ag_mOp_closed[of "b"], frule ag_mOp_closed[of "a"],
       subst ag_p_inv, assumption+, subst ag_inv_inv, assumption)
apply (simp add:ag_pOp_commute)
done

lemma (in aGroup) pOp_cancel_l:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;                    c \<plusminus> a =  c \<plusminus> b \<rbrakk> \<Longrightarrow> a = b"
apply (frule ag_mOp_closed[of "c"],
       frule aassoc[of "-\<^sub>a c" "c" "a"], assumption+,
       simp only:l_m l_zero)
apply (simp only:aassoc[THEN sym, of "-\<^sub>a c" "c" "b"],
        simp only:l_m l_zero)
done

lemma (in aGroup) pOp_cancel_r:"\<lbrakk>a \<in> carrier A; b \<in> carrier A; c \<in> carrier A;               a \<plusminus> c =  b \<plusminus> c \<rbrakk> \<Longrightarrow> a = b"
by (simp add:ag_pOp_commute pOp_cancel_l)

lemma (in aGroup) ag_eq_diffzero:"\<lbrakk>a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow>
                       (a = b) = (a \<plusminus> (-\<^sub>a b) = \<zero>)"
apply (rule iffI)
 apply (simp add:ag_r_inv1)
 apply (frule ag_mOp_closed[of "b"])
 apply (simp add:ag_pOp_commute[of "a" "-\<^sub>a b"])
 apply (subst ag_inv_unique[of "-\<^sub>a b" "a"], assumption+,
        simp add:ag_inv_inv)
done

lemma (in aGroup) ag_eq_diffzero1:"\<lbrakk>a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow>
                       (a = b) = ((-\<^sub>a a) \<plusminus> b = \<zero>)"
apply (frule ag_mOp_closed[of a],
       simp add:ag_pOp_commute)
apply (subst ag_eq_diffzero[THEN sym], assumption+)
apply (rule iffI, rule sym, assumption)
apply (rule sym, assumption)
done

lemma (in aGroup) ag_neq_diffnonzero:"\<lbrakk>a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow>
         (a \<noteq> b) = (a \<plusminus> (-\<^sub>a b) \<noteq>  \<zero>)"
apply (rule iffI)
 apply (rule contrapos_pp, simp+)
 apply (simp add:ag_eq_diffzero[THEN sym])
apply (rule contrapos_pp, simp+)
 apply (simp add:ag_r_inv1)
done

lemma (in aGroup) ag_plus_zero:"\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow>
                     (x = -\<^sub>a y)  = (x \<plusminus> y = \<zero>)"
apply (rule iffI)
 apply (simp add:ag_l_inv1)
apply (simp add:ag_pOp_commute[of "x" "y"])
apply (rule ag_inv_unique[of "y" "x"], assumption+)
done

lemma (in aGroup) asubg_nsubg:"A +> H \<Longrightarrow>  (b_ag A) \<triangleright> H"
apply (cut_tac b_ag_group)
apply (simp add:asubGroup_def)
apply (rule Group.cond_nsg[of "b_ag A" "H"], assumption+)
apply (rule ballI)+
apply(simp add:agop_gop agiop_giop)
 apply (frule Group.sg_subset[of "b_ag A" "H"], assumption)
 apply (simp add:ag_carrier_carrier)
apply (frule_tac c = h in subsetD[of "H" "carrier A"], assumption+)
 apply (subst ag_pOp_commute, assumption+)
 apply (frule_tac x = a in ag_mOp_closed)
 apply (subst aassoc, assumption+, simp add:ag_r_inv1 ag_r_zero)
done

lemma (in aGroup) subg_asubg:"b_ag G \<guillemotright> H \<Longrightarrow> G +> H"
apply (simp add:asubGroup_def)
done

lemma (in aGroup) asubg_test:"\<lbrakk>H \<subseteq> carrier A; H \<noteq> {};
               \<forall>a\<in>H. \<forall>b\<in>H. (a \<plusminus> (-\<^sub>a b) \<in> H)\<rbrakk> \<Longrightarrow> A +> H"
apply (simp add:asubGroup_def) apply (cut_tac b_ag_group)
apply (rule Group.sg_condition [of "b_ag A" "H"], assumption+)
 apply (simp add:ag_carrier_carrier) apply assumption
apply (rule allI)+ apply (rule impI)
apply (simp add:agop_gop agiop_giop)
done

lemma (in aGroup) asubg_zero:"A +> {\<zero>}"
apply (rule asubg_test[of "{\<zero>}"])
 apply (simp add:ag_inc_zero)
 apply simp
 apply (simp, cut_tac ag_inc_zero, simp add:ag_r_inv1)
done

lemma (in aGroup) asubg_whole:"A +> carrier A"
apply (rule asubg_test[of "carrier A"])
apply (simp,
       cut_tac ag_inc_zero, simp add:nonempty)
apply ((rule ballI)+,
       rule ag_pOp_closed, assumption,
       rule_tac x = b in ag_mOp_closed, assumption)
done

lemma (in aGroup) Ag_ind_carrier:"bij_to f (carrier A) (D::'d set) \<Longrightarrow>
               carrier (Ag_ind A f) = f ` (carrier A)"
by (simp add:Ag_ind_def)

lemma (in aGroup) Ag_ind_aGroup:"\<lbrakk>f \<in> carrier A \<rightarrow> D;
      bij_to f (carrier A) (D::'d set)\<rbrakk> \<Longrightarrow> aGroup (Ag_ind A f)"
apply (simp add:bij_to_def, frule conjunct1, frule conjunct2, fold bij_to_def)
apply (simp add:aGroup_def)
 apply (rule conjI)
 apply (rule Pi_I)+
 apply (simp add:Ag_ind_carrier surj_to_def)
 apply (frule_tac b = x in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = xa in invfun_mem1[of "f" "carrier A" "D"], assumption+)
apply (simp add:Ag_ind_def)
 apply (rule funcset_mem[of "f" "carrier A" "D"], assumption)
 apply (simp add:ag_pOp_closed)

 apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add: Ag_ind_carrier surj_to_def)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = b in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = c in invfun_mem1[of "f" "carrier A" "D"], assumption+)
 apply (simp add:Ag_ind_def)
 apply (frule_tac x = "invfun (carrier A) D f a" and
                  y = "invfun (carrier A) D f b" in ag_pOp_closed, assumption+,
        frule_tac x = "invfun (carrier A) D f b" and
                  y = "invfun (carrier A) D f c" in ag_pOp_closed, assumption+)
 apply (simp add:Pi_def)
 apply (unfold bij_to_def, frule conjunct1, fold bij_to_def)
 apply (simp add:invfun_l)
 apply (subst injective_iff[of "f" "carrier A", THEN sym], assumption)
 apply (simp add:ag_pOp_closed)+
 apply (simp add:ag_pOp_assoc)

apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:Ag_ind_def)
 apply (subst injective_iff[of "f" "carrier A", THEN sym], assumption)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = b in invfun_mem1[of "f" "carrier A" "D"], assumption+)
       apply (simp add:surj_to_def) apply (simp add:surj_to_def)

 apply (simp add:surj_to_def)
 apply (frule_tac b = b in invfun_mem1[of "f" "carrier A" "D"], assumption+)
 apply (simp add:ag_pOp_closed)

 apply (simp add:surj_to_def)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = b in invfun_mem1[of "f" "carrier A" "D"], assumption+)
       apply (simp add:ag_pOp_closed)

 apply (simp add:surj_to_def)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+,
        frule_tac b = b in invfun_mem1[of "f" "carrier A" "D"], assumption+)
       apply (simp add:ag_pOp_commute)

apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Ag_ind_def surj_to_def)
 apply (rule funcset_mem[of "f" "carrier A" "D"], assumption)
 apply (frule_tac b = x in invfun_mem1[of "f" "carrier A" "D"], assumption+)
 apply (simp add:ag_mOp_closed)

apply (rule conjI)
 apply (rule allI, rule impI)
 apply (simp add:Ag_ind_def surj_to_def)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+)

 apply (frule_tac x = "invfun (carrier A) D f a" in ag_mOp_closed)
 apply (simp add:Pi_def)
 apply (subst injective_iff[of "f" "carrier A", THEN sym], assumption)
 apply (unfold bij_to_def, frule conjunct1, fold bij_to_def)
 apply (simp add:invfun_l)
 apply (simp add:ag_pOp_closed)
 apply (simp add:ag_inc_zero)
 apply (unfold bij_to_def, frule conjunct1, fold bij_to_def)
 apply (simp add:invfun_l l_m)

apply (rule conjI)
 apply (simp add:Ag_ind_def surj_to_def)
 apply (rule funcset_mem[of "f" "carrier A" "D"], assumption)
 apply (simp add:ag_inc_zero)

apply (rule allI, rule impI)
  apply (simp add:Ag_ind_def surj_to_def)
  apply (cut_tac ag_inc_zero, simp add:funcset_mem del:Pi_I)
  apply (unfold bij_to_def, frule conjunct1, fold bij_to_def)
  apply (simp add:invfun_l)
 apply (frule_tac b = a in invfun_mem1[of "f" "carrier A" "D"], assumption+)
 apply (simp add:l_zero)
 apply (simp add:invfun_r)
done

subsection "Homomorphism of abelian groups"

definition
  aHom :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme] \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "aHom A B = {f. f \<in> carrier A \<rightarrow> carrier B \<and> f \<in> extensional (carrier A) \<and>
               (\<forall>a\<in>carrier A. \<forall>b\<in>carrier A. f (a \<plusminus>\<^bsub>A\<^esub> b) = (f a) \<plusminus>\<^bsub>B\<^esub> (f b))}"

definition
  compos :: "[('a, 'm) aGroup_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c" where
  "compos A g f = compose (carrier A) g f"

definition
  ker :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme] \<Rightarrow> ('a \<Rightarrow> 'b)
        \<Rightarrow> 'a set" ("(3ker\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "ker\<^bsub>F,G\<^esub> f = {a. a \<in> carrier F \<and> f a = (\<zero>\<^bsub>G\<^esub>)}"

definition
 injec :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3injec\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "injec\<^bsub>F,G\<^esub> f \<longleftrightarrow> f \<in> aHom F G \<and> ker\<^bsub>F,G\<^esub> f = {\<zero>\<^bsub>F\<^esub>}"

definition
  surjec :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3surjec\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "surjec\<^bsub>F,G\<^esub> f \<longleftrightarrow> f \<in> aHom F G \<and> surj_to f (carrier F) (carrier G)"

definition
  bijec :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3bijec\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "bijec\<^bsub>F,G\<^esub> f \<longleftrightarrow> injec\<^bsub>F,G\<^esub> f \<and> surjec\<^bsub>F,G\<^esub> f"

definition
  ainvf :: "[('a, 'm) aGroup_scheme, ('b, 'm1) aGroup_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> ('b \<Rightarrow> 'a)"             ("(3ainvf\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "ainvf\<^bsub>F,G\<^esub> f = invfun (carrier F) (carrier G) f"

lemma aHom_mem:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
                       f a \<in> carrier G"
apply (simp add:aHom_def) apply (erule conjE)+
apply (simp add:Pi_def)
done

lemma aHom_func:"f \<in> aHom F G \<Longrightarrow> f \<in> carrier F \<rightarrow> carrier G"
by (simp add:aHom_def)

lemma aHom_add:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G; a \<in> carrier F;
 b \<in> carrier F\<rbrakk> \<Longrightarrow> f (a \<plusminus>\<^bsub>F\<^esub> b) = (f a) \<plusminus>\<^bsub>G\<^esub> (f b)"
apply (simp add:aHom_def)
done

lemma aHom_0_0:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G\<rbrakk> \<Longrightarrow> f (\<zero>\<^bsub>F\<^esub>) = \<zero>\<^bsub>G\<^esub>"
apply (frule aGroup.ag_inc_zero [of "F"])
apply (subst aGroup.ag_l_zero [THEN sym, of "F" "\<zero>\<^bsub>F\<^esub>"], assumption+)
apply (simp add:aHom_add)
apply (frule aGroup.ag_l_zero [THEN sym, of "F" "\<zero>\<^bsub>F\<^esub>"], assumption+)
apply (subgoal_tac "f (\<zero>\<^bsub>F\<^esub>) = f (\<zero>\<^bsub>F\<^esub> \<plusminus>\<^bsub>F\<^esub> \<zero>\<^bsub>F\<^esub>)") prefer 2 apply simp
apply (thin_tac "\<zero>\<^bsub>F\<^esub> = \<zero>\<^bsub>F\<^esub> \<plusminus>\<^bsub>F\<^esub> \<zero>\<^bsub>F\<^esub>")
apply (simp add:aHom_add) apply (frule sym)
apply (thin_tac "f \<zero>\<^bsub>F\<^esub> = f \<zero>\<^bsub>F\<^esub> \<plusminus>\<^bsub>G\<^esub> f \<zero>\<^bsub>F\<^esub>")
apply (frule aHom_mem[of "F" "G" "f" "\<zero>\<^bsub>F\<^esub>"], assumption+)
apply (frule aGroup.ag_mOp_closed[of "G" "f \<zero>\<^bsub>F\<^esub>"], assumption+)
apply (frule aGroup.aassoc[of "G" "-\<^sub>a\<^bsub>G\<^esub> (f \<zero>\<^bsub>F\<^esub>)" "f \<zero>\<^bsub>F\<^esub>" "f \<zero>\<^bsub>F\<^esub>"], assumption+)
apply (simp add:aGroup.l_m aGroup.l_zero)
done

lemma ker_inc_zero:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G\<rbrakk> \<Longrightarrow> \<zero>\<^bsub>F\<^esub> \<in> ker\<^bsub>F,G\<^esub> f"
by (frule aHom_0_0[of "F" "G" "f"], assumption+,
       simp add:ker_def, simp add:aGroup.ag_inc_zero [of "F"])

lemma aHom_inv_inv:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
                         f (-\<^sub>a\<^bsub>F\<^esub> a) = -\<^sub>a\<^bsub>G\<^esub> (f a)"
apply (frule aGroup.ag_l_inv1 [of "F" "a"], assumption+,
       frule sym, thin_tac "-\<^sub>a\<^bsub>F\<^esub> a \<plusminus>\<^bsub>F\<^esub> a = \<zero>\<^bsub>F\<^esub>",
       frule aHom_0_0[of "F" "G" "f"], assumption+,
       frule aGroup.ag_mOp_closed[of "F" "a"], assumption+)
 apply (simp add:aHom_add, thin_tac "\<zero>\<^bsub>F\<^esub> = -\<^sub>a\<^bsub>F\<^esub> a \<plusminus>\<^bsub>F\<^esub> a")
 apply (frule aHom_mem[of "F" "G" "f" "-\<^sub>a\<^bsub>F\<^esub> a"], assumption+,
        frule aHom_mem[of "F" "G" "f" "a"], assumption+,
        simp only:aGroup.ag_pOp_commute[of "G" "f (-\<^sub>a\<^bsub>F\<^esub> a)" "f a"])
 apply (rule aGroup.ag_inv_unique[of "G"], assumption+)
done

lemma aHom_compos:"\<lbrakk>aGroup L; aGroup M; aGroup N; f \<in> aHom L M; g \<in> aHom M N \<rbrakk>
  \<Longrightarrow> compos L g f \<in> aHom L N"
apply (simp add:aHom_def [of "L" "N"])
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:compos_def compose_def)
 apply (rule aHom_mem [of "M" "N" "g"], assumption+)
 apply (simp add:aHom_mem [of "L" "M" "f"])
apply (rule conjI)
 apply (simp add:compos_def compose_def extensional_def)
apply (rule ballI)+
 apply (simp add:compos_def compose_def)
 apply (simp add:aGroup.ag_pOp_closed)
 apply (simp add:aHom_add)
 apply (rule aHom_add, assumption+)
 apply (simp add:aHom_mem)+
done

lemma aHom_compos_assoc:"\<lbrakk>aGroup K; aGroup L; aGroup M; aGroup N; f \<in> aHom K L;
      g \<in> aHom L M; h \<in> aHom M N \<rbrakk>  \<Longrightarrow>
      compos K h (compos K g f) = compos K (compos L h g) f"
apply (simp add:compos_def compose_def)
apply (rule funcset_eq[of _ "carrier K"])
apply (simp add:restrict_def extensional_def)
apply (simp add:restrict_def extensional_def)
apply (rule ballI, simp)
apply (simp add:aHom_mem)
done

lemma injec_inj_on:"\<lbrakk>aGroup F; aGroup G; injec\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow> inj_on f (carrier F)"
apply (simp add:inj_on_def)
 apply (rule ballI)+ apply (rule impI)
 apply (simp add:injec_def, erule conjE)
 apply (frule_tac a = x in aHom_mem[of "F" "G" "f"], assumption+,
        frule_tac a = x in aHom_mem[of "F" "G" "f"], assumption+)
 apply (frule_tac x = "f x" in aGroup.ag_r_inv1[of "G"], assumption+)
 apply (simp only:aHom_inv_inv[THEN sym, of "F" "G" "f"])
 apply (frule sym, thin_tac "f x = f y", simp)
 apply (frule_tac x = y in aGroup.ag_mOp_closed[of "F"], assumption+)
 apply (simp add:aHom_add[THEN sym], simp add:ker_def)
 apply (subgoal_tac "x \<plusminus>\<^bsub>F\<^esub> -\<^sub>a\<^bsub>F\<^esub> y \<in> {a \<in> carrier F. f a = \<zero>\<^bsub>G\<^esub>}",
        simp)
 apply (subst aGroup.ag_eq_diffzero[of "F"], assumption+)
apply (frule_tac x = x and y = "-\<^sub>a\<^bsub>F\<^esub> y" in aGroup.ag_pOp_closed[of "F"],
           assumption+)
 apply simp apply blast
done

lemma surjec_surj_to:"surjec\<^bsub>R,S\<^esub> f \<Longrightarrow> surj_to f (carrier R) (carrier S)"
by (simp add:surjec_def)

lemma compos_bijec:"\<lbrakk>aGroup E; aGroup F; aGroup G; bijec\<^bsub>E,F\<^esub> f; bijec\<^bsub>F,G\<^esub> g\<rbrakk> \<Longrightarrow>
                     bijec\<^bsub>E,G\<^esub> (compos E g f)"
apply (simp add:bijec_def, (erule conjE)+)
apply (rule conjI)
 apply (simp add:injec_def, (erule conjE)+)
 apply (simp add:aHom_compos[of "E" "F" "G" "f" "g"])
 apply (rule equalityI, rule subsetI, simp add:ker_def, erule conjE)
 apply (simp add:compos_def compose_def)
 apply (frule_tac a = x in aHom_mem[of "E" "F" "f"], assumption+)
 apply (subgoal_tac "(f x) \<in> {a \<in> carrier F. g a = \<zero>\<^bsub>G\<^esub>}", simp)
 apply (subgoal_tac "x \<in> {a \<in> carrier E. f a = \<zero>\<^bsub>F\<^esub>}", simp)
 apply blast apply blast
 apply (rule subsetI, simp)
 apply (simp add:ker_def compos_def compose_def)
 apply (simp add:aGroup.ag_inc_zero) apply (simp add:aHom_0_0)

apply (simp add:surjec_def, (erule conjE)+)
 apply (simp add:aHom_compos)
 apply (simp add:aHom_def, (erule conjE)+) apply (simp add:compos_def)
 apply (rule compose_surj[of "f" "carrier E" "carrier F" "g" "carrier G"],
            assumption+)
done

lemma ainvf_aHom:"\<lbrakk>aGroup F; aGroup G; bijec\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow>
                      ainvf\<^bsub>F,G\<^esub> f \<in> aHom G F"
apply (subst aHom_def, simp)
 apply (simp add:ainvf_def)
 apply (simp add:bijec_def, erule conjE)
 apply (frule injec_inj_on[of "F" "G" "f"], assumption+)
 apply (simp add:surjec_def, (erule conjE)+)
 apply (simp add:aHom_def, (erule conjE)+)
 apply (frule inv_func[of "f" "carrier F" "carrier G"], assumption+, simp)
apply (rule conjI)
 apply (simp add:invfun_def)
apply (rule ballI)+
 apply (frule_tac x = a in funcset_mem[of "Ifn F G f" "carrier G" "carrier F"],
      assumption+,
      frule_tac x = b in funcset_mem[of "Ifn F G f" "carrier G" "carrier F"],
      assumption+,
      frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "G"], assumption+,
      frule_tac x = "a \<plusminus>\<^bsub>G\<^esub> b" in funcset_mem[of "Ifn F G f" "carrier G"
       "carrier F"], assumption+)
 apply (frule_tac a = "(Ifn F G f) a" and b = "(Ifn F G f) b" in
           aHom_add[of "F" "G" "f"], assumption+, simp add:injec_def,
           assumption+,
           thin_tac "\<forall>a\<in>carrier F. \<forall>b\<in>carrier F. f (a \<plusminus>\<^bsub>F\<^esub> b) = f a \<plusminus>\<^bsub>G\<^esub> f b")
 apply (simp add:invfun_r[of "f" "carrier F" "carrier G"])
 apply (frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "G"], assumption+) apply (frule_tac b = "a \<plusminus>\<^bsub>G\<^esub> b" in invfun_r[of "f" "carrier F" "carrier G"],
           assumption+)
 apply (simp add:inj_on_def)
 apply (frule_tac x = "(Ifn F G f) a" and y = "(Ifn F G f) b" in
          aGroup.ag_pOp_closed, assumption+)
 apply (frule_tac x = "(Ifn F G f) (a \<plusminus>\<^bsub>G\<^esub> b)" in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier F. \<forall>y\<in>carrier F. f x = f y \<longrightarrow> x = y")
 apply (frule_tac x = "(Ifn F G f) a \<plusminus>\<^bsub>F\<^esub> (Ifn F G f) b" in bspec,
            assumption,
        thin_tac "\<forall>y\<in>carrier F.
              f ((Ifn F G f) (a \<plusminus>\<^bsub>G\<^esub> b)) = f y \<longrightarrow> (Ifn F G f) (a \<plusminus>\<^bsub>G\<^esub> b) = y")
 apply simp
done

lemma ainvf_bijec:"\<lbrakk>aGroup F; aGroup G; bijec\<^bsub>F,G\<^esub> f\<rbrakk> \<Longrightarrow> bijec\<^bsub>G,F\<^esub> (ainvf\<^bsub>F,G\<^esub> f)"
apply (subst bijec_def)
apply (simp add:injec_def surjec_def)
apply (simp add:ainvf_aHom)
apply (rule conjI)
 apply (rule equalityI)
 apply (rule subsetI, simp add:ker_def, erule conjE)
 apply (simp add:ainvf_def)
 apply (simp add:bijec_def,(erule conjE)+, simp add:surjec_def,
         (erule conjE)+, simp add:aHom_def, (erule conjE)+)
 apply (frule injec_inj_on[of "F" "G" "f"], assumption+)
 apply (subst invfun_r[THEN sym, of "f" "carrier F" "carrier G"], assumption+)
 apply (simp add:injec_def, (erule conjE)+, simp add:aHom_0_0)

 apply (rule subsetI, simp add:ker_def)
 apply (simp add:aGroup.ex_zero)
 apply (frule ainvf_aHom[of "F" "G" "f"], assumption+)
 apply (simp add:aHom_0_0)

apply (frule ainvf_aHom[of "F" "G" "f"], assumption+,
        simp add:aHom_def, (erule conjE)+,
       rule surj_to_test[of "ainvf\<^bsub>F,G\<^esub> f" "carrier G" "carrier F"],
        assumption+)
 apply (rule ballI,
        thin_tac "\<forall>a\<in>carrier G. \<forall>b\<in>carrier G.
               (ainvf\<^bsub>F,G\<^esub> f) (a \<plusminus>\<^bsub>G\<^esub> b) = (ainvf\<^bsub>F,G\<^esub> f) a \<plusminus>\<^bsub>F\<^esub> (ainvf\<^bsub>F,G\<^esub> f) b")
 apply (simp add:bijec_def, erule conjE)
  apply (frule injec_inj_on[of "F" "G" "f"], assumption+)
  apply (simp add:surjec_def aHom_def, (erule conjE)+)
  apply (subst ainvf_def)
 apply (frule_tac a = b in invfun_l[of "f" "carrier F" "carrier G"],
                  assumption+,
        frule_tac x = b in funcset_mem[of "f" "carrier F" "carrier G"],
                  assumption+, blast)
done

lemma ainvf_l:"\<lbrakk>aGroup E; aGroup F; bijec\<^bsub>E,F\<^esub> f; x \<in> carrier E\<rbrakk> \<Longrightarrow>
                      (ainvf\<^bsub>E,F\<^esub> f) (f x) = x"
apply (simp add:bijec_def, erule conjE)
apply (frule injec_inj_on[of "E" "F" "f"], assumption+)
apply (simp add:surjec_def aHom_def, (erule conjE)+)
apply (frule invfun_l[of "f" "carrier E" "carrier F" "x"], assumption+)
apply (simp add:ainvf_def)
done

lemma (in aGroup) aI_aHom:"aI\<^bsub>A\<^esub> \<in> aHom A A"
by (simp add:aHom_def ag_idmap_def ag_idmap_def ag_pOp_closed)

lemma compos_aI_l:"\<lbrakk>aGroup A; aGroup B; f \<in> aHom A B\<rbrakk> \<Longrightarrow> compos A aI\<^bsub>B\<^esub> f = f"
apply (simp add:compos_def)
apply (rule funcset_eq[of _ "carrier A"])
 apply (simp add:compose_def extensional_def)
 apply (simp add:aHom_def)
apply (rule ballI)
 apply (frule_tac a = x in aHom_mem[of "A" "B" "f"], assumption+)
 apply (simp add:compose_def ag_idmap_def)
done

lemma compos_aI_r:"\<lbrakk>aGroup A; aGroup B; f \<in> aHom A B\<rbrakk> \<Longrightarrow> compos A f aI\<^bsub>A\<^esub> = f"
apply (simp add:compos_def)
apply (rule funcset_eq[of _ "carrier A"])
 apply (simp add:compose_def extensional_def)
 apply (simp add:aHom_def)
apply (rule ballI)
 apply (simp add:compose_def ag_idmap_def)
done

lemma compos_aI_surj:"\<lbrakk>aGroup A; aGroup B; f \<in> aHom A B; g \<in> aHom B A;
                      compos A g f = aI\<^bsub>A\<^esub>\<rbrakk> \<Longrightarrow> surjec\<^bsub>B,A\<^esub> g"
apply (simp add:surjec_def)
apply (rule surj_to_test[of "g" "carrier B" "carrier A"])
 apply (simp add:aHom_def)
apply (rule ballI)
 apply (subgoal_tac "compos A g f b = aI\<^bsub>A\<^esub> b",
        thin_tac "compos A g f = aI\<^bsub>A\<^esub>")
 apply (simp add:compos_def compose_def ag_idmap_def)
 apply (frule_tac a = b in aHom_mem[of "A" "B" "f"], assumption+, blast)
 apply simp
done

lemma compos_aI_inj:"\<lbrakk>aGroup A; aGroup B; f \<in> aHom A B; g \<in> aHom B A;
                      compos A g f = aI\<^bsub>A\<^esub>\<rbrakk> \<Longrightarrow> injec\<^bsub>A,B\<^esub> f"
apply (simp add:injec_def)
apply (simp add:ker_def)
apply (rule equalityI)
 apply (rule subsetI, simp, erule conjE)
 apply (subgoal_tac "compos A g f x = aI\<^bsub>A\<^esub> x",
        thin_tac "compos A g f = aI\<^bsub>A\<^esub>")
 apply (simp add:compos_def compose_def)
 apply (simp add:aHom_0_0 ag_idmap_def) apply simp

 apply (rule subsetI, simp)
 apply (simp add:aGroup.ag_inc_zero aHom_0_0)
done

lemma (in aGroup) Ag_ind_aHom:"\<lbrakk>f \<in> carrier A \<rightarrow> D;
      bij_to f (carrier A) (D::'d set)\<rbrakk> \<Longrightarrow> Agii A f \<in> aHom A (Ag_ind A f)"
apply (simp add:aHom_def)
 apply (unfold bij_to_def, frule conjunct1, frule conjunct2, fold bij_to_def)
 apply (simp add:Ag_ind_carrier surj_to_def)
apply (rule conjI)
 apply (simp add:Agii_def Pi_def)
 apply (simp add:Agii_def)
 apply (simp add:Ag_ind_def Pi_def)
 apply (unfold bij_to_def, frule conjunct1, fold bij_to_def)
 apply (simp add:invfun_l)
 apply (simp add:ag_pOp_closed)
done

lemma (in aGroup) Agii_mem:"\<lbrakk>f \<in> carrier A \<rightarrow> D; x \<in> carrier A;
      bij_to f (carrier A) (D::'d set)\<rbrakk> \<Longrightarrow> Agii A f x \<in> carrier (Ag_ind A f)"
apply (simp add:Agii_def Ag_ind_carrier)
done

lemma Ag_ind_bijec:"\<lbrakk>aGroup A; f \<in> carrier A \<rightarrow> D;
      bij_to f (carrier A) (D::'d set)\<rbrakk> \<Longrightarrow> bijec\<^bsub>A, (Ag_ind A f)\<^esub> (Agii A f)"
apply (frule aGroup.Ag_ind_aHom[of "A" "f" "D"], assumption+)
apply (frule aGroup.Ag_ind_aGroup[of "A" "f" "D"], assumption+)
apply (simp add:bijec_def)
 apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def, erule conjE)
apply (frule aHom_0_0[of "A" "Ag_ind A f" "Agii A f"], assumption+)
 apply (rotate_tac -2, frule sym, thin_tac "Agii A f x = \<zero>\<^bsub>Ag_ind A f\<^esub>", simp)
 apply (frule aGroup.ag_inc_zero[of "A"], simp add:Agii_def)
 apply (unfold bij_to_def, frule conjunct2, fold bij_to_def)
 apply (frule aGroup.ag_inc_zero[of "A"])
 apply (simp add:injective_iff[THEN sym, of "f" "carrier A" "\<zero>\<^bsub>A\<^esub>"])
 apply (rule subsetI, simp)
 apply (subst ker_def, simp)
 apply (simp add:aGroup.ag_inc_zero, simp add:aHom_0_0)

apply (subst surjec_def)
apply (unfold bij_to_def, frule conjunct1, fold bij_to_def, simp)
 apply (simp add:aGroup.Ag_ind_carrier surj_to_def Agii_def)
done

definition
  aimg :: "[('b, 'm1) aGroup_scheme, _, 'b \<Rightarrow> 'a]
            \<Rightarrow> 'a aGroup"  ("(3aimg\<^bsub>_,_\<^esub> _)" [82,82,83]82) where
  "aimg\<^bsub>F,A\<^esub> f = A \<lparr> carrier := f ` (carrier F), pop := pop A, mop := mop A,
                  zero := zero A\<rparr>"

lemma ker_subg:"\<lbrakk>aGroup F; aGroup G; f \<in> aHom F G \<rbrakk> \<Longrightarrow> F +> ker\<^bsub>F,G\<^esub> f"
apply (rule aGroup.asubg_test, assumption+)
apply (rule subsetI)
 apply (simp add:ker_def)
apply (simp add:ker_def)
apply (frule aHom_0_0 [of "F" "G" "f"], assumption+)
apply (frule aGroup.ex_zero [of "F"]) apply blast
apply (rule ballI)+
apply (simp add:ker_def) apply (erule conjE)+
apply (frule_tac x = b in aGroup.ag_mOp_closed[of "F"], assumption+)
apply (rule conjI)
apply (rule aGroup.ag_pOp_closed, assumption+)
apply (simp add:aHom_add)
apply (simp add:aHom_inv_inv)
apply (simp add:aGroup.ag_inv_zero[of "G"])
apply (cut_tac aGroup.ex_zero[of "G"], simp add:aGroup.l_zero)
apply assumption
done

subsection "Quotient abelian group"

definition
  ar_coset :: "['a, _ , 'a set] \<Rightarrow> 'a set" (** a_rcs **)
     ("(3_ \<uplus>\<^bsub>_\<^esub> _)" [66,66,67]66) where
  "ar_coset a A H = H \<bullet>\<^bsub>(b_ag A)\<^esub> a"

definition
  set_ar_cos :: "[_ , 'a set] \<Rightarrow> 'a set set" where
  "set_ar_cos A I = {X. \<exists>a\<in>carrier A. X = ar_coset a A I}"

definition
  aset_sum :: "[_ , 'a set, 'a set] \<Rightarrow> 'a set" where
  "aset_sum A H K = s_top (b_ag A) H K"

abbreviation
  ASBOP1  (infix "\<minusplus>\<index>" 60) where
  "H \<minusplus>\<^bsub>A\<^esub> K == aset_sum A H K"

lemma (in aGroup) ag_a_in_ar_cos:"\<lbrakk>A +> H; a \<in> carrier A\<rbrakk> \<Longrightarrow> a \<in> a \<uplus>\<^bsub>A\<^esub> H"
apply (simp add:ar_coset_def)
apply (simp add:asubGroup_def)
apply (cut_tac b_ag_group)
apply (rule Group.a_in_rcs[of "b_ag A" "H" "a"], assumption+)
apply (simp add:ag_carrier_carrier[THEN sym])
done

lemma (in aGroup) r_cos_subset:"\<lbrakk>A +> H; X \<in> set_rcs (b_ag A) H\<rbrakk> \<Longrightarrow>
                   X \<subseteq> carrier A"
apply (simp add:asubGroup_def set_rcs_def)
apply (erule bexE)
apply (cut_tac  b_ag_group)
apply (frule_tac a = a in Group.rcs_subset[of "b_ag A" "H"], assumption+)
apply (simp add:ag_carrier_carrier)
done

lemma (in aGroup) asubg_costOp_commute:"\<lbrakk>A +> H; x \<in> set_rcs (b_ag A) H;
       y \<in> set_rcs (b_ag A) H\<rbrakk> \<Longrightarrow>
             c_top (b_ag A) H x y = c_top (b_ag A) H y x"
apply (simp add:set_rcs_def, (erule bexE)+, simp)
apply (cut_tac b_ag_group)
apply (subst Group.c_top_welldef[THEN sym], assumption+,
       simp add:asubg_nsubg,
       (simp add:ag_carrier_carrier)+)
apply (subst Group.c_top_welldef[THEN sym], assumption+,
       simp add:asubg_nsubg,
       (simp add:ag_carrier_carrier)+)
apply (simp add:agop_gop)
 apply (simp add:ag_pOp_commute)
done

lemma (in aGroup) Subg_Qgroup:"A +> H \<Longrightarrow> aGroup (aqgrp A H)"
apply (frule asubg_nsubg[of "H"])
apply (cut_tac b_ag_group)
apply (simp add:aGroup_def)
 apply (simp add:aqgrp_def)
 apply (simp add:Group.Qg_top [of "b_ag A" "H"])
 apply (simp add:Group.Qg_iop [of "b_ag A" "H"])
 apply (frule Group.nsg_sg[of "b_ag A" "H"], assumption+,
        simp add:Group.unit_rcs_in_set_rcs[of "b_ag A" "H"])
apply (simp add:Group.Qg_tassoc)
apply (simp add:asubg_costOp_commute)
apply (simp add:Group.Qg_i[of "b_ag A" "H"])
apply (simp add:Group.Qg_unit[of "b_ag A" "H"])
done

lemma (in aGroup) plus_subgs:"\<lbrakk>A +> H1; A +> H2\<rbrakk> \<Longrightarrow> A +> H1 \<minusplus> H2"
apply (simp add:aset_sum_def)
 apply (frule asubg_nsubg[of "H2"])
 apply (simp add:asubGroup_def[of _ "H1"])
apply (cut_tac "b_ag_group")
apply (frule Group.smult_sg_nsg[of "b_ag A" "H1" "H2"], assumption+)
apply (simp add:asubGroup_def)
done

lemma (in aGroup) set_sum:"\<lbrakk>H \<subseteq> carrier A; K \<subseteq> carrier A\<rbrakk> \<Longrightarrow>
                    H \<minusplus> K = {x. \<exists>h\<in>H. \<exists>k\<in>K. x = h \<plusminus> k}"
 apply (cut_tac b_ag_group)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:aset_sum_def)
 apply (simp add:agop_gop[THEN sym] s_top_def, (erule bexE)+,
        frule sym, thin_tac "xa \<cdot>\<^bsub>b_ag A\<^esub> y = x", simp, blast)
 apply (rule subsetI, simp add:aset_sum_def, (erule bexE)+)
 apply (frule_tac c = h in subsetD[of H "carrier A"], assumption+,
        frule_tac c = k in subsetD[of K "carrier A"], assumption+)
 apply (simp add:agop_gop[THEN sym], simp add:s_top_def, blast)
done

lemma (in aGroup) mem_set_sum:"\<lbrakk>H \<subseteq> carrier A; K \<subseteq> carrier A;
                  x \<in> H \<minusplus> K \<rbrakk> \<Longrightarrow> \<exists>h\<in>H. \<exists>k\<in>K. x = h \<plusminus> k"
by (simp add:set_sum)

lemma (in aGroup) mem_sum_subgs:"\<lbrakk>A +> H; A +> K; h \<in> H; k \<in> K\<rbrakk> \<Longrightarrow>
                    h \<plusminus> k \<in> H \<minusplus> K"
apply (frule asubg_subset[of H],
       frule asubg_subset[of K],
       simp add:set_sum, blast)
done

lemma (in aGroup) aqgrp_carrier:"A +> H \<Longrightarrow>
                   set_rcs (b_ag A ) H = set_ar_cos A H"
apply (simp add:set_ar_cos_def)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:ar_coset_def set_rcs_def)
done

lemma (in aGroup) unit_in_set_ar_cos:"A +> H \<Longrightarrow> H \<in> set_ar_cos A H"
apply (simp add:aqgrp_carrier[THEN sym])
apply (cut_tac b_ag_group) apply (simp add:asubGroup_def)
apply (simp add:Group.unit_rcs_in_set_rcs[of "b_ag A" "H"])
done

lemma (in aGroup) aqgrp_pOp_maps:"\<lbrakk>A +> H; a \<in> carrier A; b \<in> carrier A\<rbrakk> \<Longrightarrow>
      pop (aqgrp A H) (a \<uplus>\<^bsub>A\<^esub> H) (b \<uplus>\<^bsub>A\<^esub> H) = (a \<plusminus> b) \<uplus>\<^bsub>A\<^esub> H"
apply (simp add:aqgrp_def ar_coset_def)
apply (cut_tac b_ag_group)
apply (frule asubg_nsubg)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (subst Group.c_top_welldef [THEN sym], assumption+)
apply (simp add:agop_gop)
done

lemma (in aGroup) aqgrp_mOp_maps:"\<lbrakk>A +> H; a \<in> carrier A\<rbrakk> \<Longrightarrow>
                   mop (aqgrp A H) (a \<uplus>\<^bsub>A\<^esub> H) = (-\<^sub>a a) \<uplus>\<^bsub>A\<^esub> H"
apply (simp add:aqgrp_def ar_coset_def)
apply (cut_tac b_ag_group)
apply (frule asubg_nsubg)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (subst Group.c_iop_welldef, assumption+)
apply (simp add:agiop_giop)
done

lemma (in aGroup) aqgrp_zero:"A +> H \<Longrightarrow> zero (aqgrp A H) = H"
apply (simp add:aqgrp_def)
done

lemma (in aGroup) arcos_fixed:"\<lbrakk>A +> H; a \<in> carrier A; h \<in> H \<rbrakk> \<Longrightarrow>
                              a \<uplus>\<^bsub>A\<^esub> H = (h \<plusminus> a) \<uplus>\<^bsub>A\<^esub> H"
 apply (cut_tac b_ag_group)
 apply (simp add:agop_gop[THEN sym])
 apply (simp add:ag_carrier_carrier[THEN sym])
 apply (simp add:ar_coset_def)
 apply (simp add:asubGroup_def)
 apply (simp add:Group.rcs_fixed1[of "b_ag A" "H"])
done

definition
  rind_hom :: "[('a, 'more) aGroup_scheme, ('b, 'more1) aGroup_scheme,
                ('a  \<Rightarrow> 'b)] \<Rightarrow> ('a set  \<Rightarrow> 'b )" where
  "rind_hom A B f = (\<lambda>X\<in>(set_ar_cos A (ker\<^bsub>A,B\<^esub> f)). f (SOME x. x \<in> X))"

abbreviation
  RIND_HOM  ("(3_\<degree>\<^bsub>_,_\<^esub>)" [82,82,83]82)  where
  "f\<degree>\<^bsub>F,G\<^esub> == rind_hom F G f"
                                                          (* tOp \<rightarrow> pOp *)

section "Direct product and direct sum of abelian groups, in general case"

definition
  Un_carrier :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> 'a set" where
  "Un_carrier I A = \<Union>{X. \<exists>i\<in>I. X = carrier (A i)}"

definition
  carr_prodag :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> ('i  \<Rightarrow> 'a ) set" where
  "carr_prodag I A = {f. f \<in> extensional I \<and> f \<in> I \<rightarrow> (Un_carrier I A) \<and>
                                               (\<forall>i\<in>I. f i \<in> carrier (A i))}"

definition
  prod_pOp :: "['i set,  'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow>
                                 ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)" where
  "prod_pOp I A = (\<lambda>f\<in>carr_prodag I A. \<lambda>g\<in>carr_prodag I A.
                                        \<lambda>x\<in>I. (f x) \<plusminus>\<^bsub>(A x)\<^esub> (g x))"

definition
  prod_mOp :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow>
                                  ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "prod_mOp I A = (\<lambda>f\<in>carr_prodag I A. \<lambda>x\<in>I. (-\<^sub>a\<^bsub>(A x)\<^esub> (f x)))"

definition
  prod_zero :: "['i set,  'i  \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "prod_zero I A = (\<lambda>x\<in>I. \<zero>\<^bsub>(A x)\<^esub>)"

definition
  prodag :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) aGroup" where
  "prodag I A = \<lparr> carrier = carr_prodag I A,
    pop = prod_pOp I A, mop = prod_mOp I A,
    zero = prod_zero I A\<rparr>"

definition
  PRoject :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme, 'i]
                   \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a" ("(3\<pi>\<^bsub>_,_,_\<^esub>)" [82,82,83]82) where
  "PRoject I A x = (\<lambda>f \<in> carr_prodag I A. f x)"

abbreviation
  PRODag  ("(a\<Pi>\<^bsub>_\<^esub> _)" [72,73]72) where
  "a\<Pi>\<^bsub>I\<^esub> A == prodag I A"

lemma prodag_comp_i:"\<lbrakk>a \<in> carr_prodag I A; i \<in> I\<rbrakk> \<Longrightarrow> (a i) \<in> carrier (A i)"
by (simp add:carr_prodag_def)

lemma prod_pOp_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
    prod_pOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A \<rightarrow> carr_prodag I A"
apply (rule Pi_I)+
apply(rename_tac a b)
 apply (subst carr_prodag_def) apply (simp add:CollectI)
apply (rule conjI)
 apply (simp add:prod_pOp_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:prod_pOp_def)
 apply (subst Un_carrier_def) apply (simp add:CollectI)
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)")
 apply (simp add:carr_prodag_def) apply (erule conjE)+
 apply (thin_tac "a \<in> I \<rightarrow> Un_carrier I A")
 apply (thin_tac "b \<in> I \<rightarrow> Un_carrier I A")
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>i\<in>I. a i \<in> carrier (A i)",
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>i\<in>I. b i \<in> carrier (A i)")
 apply (frule_tac x = "a x" and y = "b x" in aGroup.ag_pOp_closed, assumption+)
 apply blast
apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (rule_tac A = "A i" and x = "a i" and y = "b i" in aGroup.ag_pOp_closed)
 apply simp
 apply (simp add:carr_prodag_def)+
done

lemma prod_pOp_mem:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); X \<in> carr_prodag I A;
 Y \<in> carr_prodag I A\<rbrakk> \<Longrightarrow> prod_pOp I A X Y \<in> carr_prodag I A"
apply (frule prod_pOp_func)
apply (frule funcset_mem[of "prod_pOp I A"
                        "carr_prodag I A" "carr_prodag I A \<rightarrow> carr_prodag I A"
                         "X"], assumption+)
apply (rule funcset_mem[of "prod_pOp I A X" "carr_prodag I A"
                           "carr_prodag I A" "Y"], assumption+)
done

lemma prod_pOp_mem_i:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); X \<in> carr_prodag I A;
 Y \<in> carr_prodag I A; i \<in> I\<rbrakk> \<Longrightarrow> prod_pOp I A X Y i = (X i) \<plusminus>\<^bsub>(A i)\<^esub> (Y i)"
apply (simp add:prod_pOp_def)
done

lemma prod_mOp_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  prod_mOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A"
apply (rule Pi_I)
 apply (simp add:prod_mOp_def carr_prodag_def)
 apply (erule conjE)+
apply (rule conjI)
 apply (rule Pi_I) apply simp
 apply (rename_tac f j)
 apply (frule_tac f = f and x = j in funcset_mem [of _ "I" "Un_carrier I A"],
                             assumption+)
 apply (thin_tac "f \<in> I \<rightarrow> Un_carrier I A")
 apply (frule_tac x = j in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)",
        frule_tac x = j in bspec, assumption,
        thin_tac "\<forall>i\<in>I. f i \<in> carrier (A i)")
 apply (thin_tac "f j \<in> Un_carrier I A")
 apply (simp add:Un_carrier_def)
 apply (frule aGroup.ag_mOp_closed, assumption+)
 apply blast
apply (rule ballI)
 apply (rule_tac A = "A i" and x = "x i" in aGroup.ag_mOp_closed)
 apply simp+
done

lemma prod_mOp_mem:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); X \<in> carr_prodag I A\<rbrakk> \<Longrightarrow>
                         prod_mOp I A X \<in> carr_prodag I A"
apply (frule prod_mOp_func)
apply (simp add:Pi_def)
done

lemma prod_mOp_mem_i:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); X \<in> carr_prodag I A; i \<in> I\<rbrakk> \<Longrightarrow>
                         prod_mOp I A X i = -\<^sub>a\<^bsub>(A i)\<^esub> (X i)"
apply (simp add:prod_mOp_def)
done

lemma prod_zero_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                           prod_zero I A \<in> carr_prodag I A"
apply (simp add:prod_zero_def prodag_def)
apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (rule Pi_I) apply simp
 apply (subgoal_tac "aGroup (A x)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. aGroup (A k)")
 apply (simp add:Un_carrier_def)
 apply (frule aGroup.ex_zero)
 apply auto
apply (frule_tac x = i in bspec, assumption,
       thin_tac "\<forall>k\<in>I. aGroup (A k)")
 apply (simp add:aGroup.ex_zero)
done

lemma prod_zero_i:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); i \<in> I\<rbrakk> \<Longrightarrow>
                           prod_zero I A i = \<zero>\<^bsub>(A i)\<^esub> "
by (simp add:prod_zero_def)

lemma carr_prodag_mem_eq:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); X \<in> carr_prodag I A;
Y \<in> carr_prodag I A; \<forall>l\<in>I. (X l) = (Y l) \<rbrakk> \<Longrightarrow> X = Y"
apply (simp add:carr_prodag_def)
apply (erule conjE)+
apply (simp add:funcset_eq)
done

lemma prod_pOp_assoc:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); a \<in> carr_prodag I A;
      b \<in> carr_prodag I A; c \<in> carr_prodag I A\<rbrakk> \<Longrightarrow>
      prod_pOp I A (prod_pOp I A a b) c =
                               prod_pOp I A a (prod_pOp I A b c)"
 apply (frule_tac X = a and Y = b in prod_pOp_mem[of "I" "A"], assumption+,
        frule_tac X = b and Y = c in prod_pOp_mem[of "I" "A"], assumption+,
        frule_tac X = "prod_pOp I A a b" and Y = c in prod_pOp_mem[of "I"
            "A"], assumption+,
        frule_tac X = a and Y = "prod_pOp I A b c" in prod_pOp_mem[of "I"
            "A"], assumption+)
 apply (rule carr_prodag_mem_eq[of "I" "A"], assumption+,
       rule ballI)
 apply (simp add:prod_pOp_mem_i)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)")
 apply (rule aGroup.ag_pOp_assoc, assumption)
 apply (simp add:prodag_comp_i)+
done

lemma prod_pOp_commute:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); a \<in> carr_prodag I A;
                           b \<in> carr_prodag I A\<rbrakk> \<Longrightarrow>
                           prod_pOp I A a b = prod_pOp I A b a"
apply (frule_tac X = a and Y = b in prod_pOp_mem[of "I" "A"], assumption+,
         frule_tac X = b and Y = a in prod_pOp_mem[of "I" "A"], assumption+)
apply (rule carr_prodag_mem_eq[of "I" "A"], assumption+,
        rule ballI)
 apply (simp add:prod_pOp_mem_i)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)",
        rule aGroup.ag_pOp_commute, assumption)
 apply (simp add:prodag_comp_i)+
done

lemma prodag_aGroup:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow> aGroup (prodag I A)"
apply (simp add:aGroup_def [of "(prodag I A)"])
apply (simp add:prodag_def)
 apply (simp add:prod_pOp_func)
 apply (simp add:prod_mOp_func)
 apply (simp add:prod_zero_func)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:prod_pOp_assoc)
apply (rule conjI)
  apply (rule allI, rule impI)+
  apply (simp add:prod_pOp_commute)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (frule_tac X = a in prod_mOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = "prod_mOp I A a" and Y = a in prod_pOp_mem[of "I" "A"],
        assumption+)
 apply (rule carr_prodag_mem_eq[of "I" "A"], assumption+)
 apply (simp add:prod_zero_func)
 apply (rule ballI)
 apply (simp add:prod_pOp_mem_i,
         simp add:prod_zero_i) apply (
         simp add:prod_mOp_mem_i)
  apply (frule_tac x = l in bspec, assumption,
         thin_tac "\<forall>k\<in>I. aGroup (A k)",
         rule aGroup.l_m, assumption+, simp add:prodag_comp_i)
apply (rule allI, rule impI)
  apply (frule_tac prod_zero_func[of "I" "A"],
         frule_tac Y = a in prod_pOp_mem[of "I" "A" "prod_zero I A"],
          assumption+)
  apply (rule carr_prodag_mem_eq[of "I" "A"], assumption+)
  apply (rule ballI)
  apply (subst prod_pOp_mem_i[of "I" "A"], assumption+,
         subst prod_zero_i[of "I" "A"], assumption+)
  apply (frule_tac x = l in bspec, assumption,
         rule aGroup.l_zero, assumption+,
         simp add:prodag_comp_i)
done

lemma prodag_carrier:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
            carrier (prodag I A) = carr_prodag I A"
by (simp add:prodag_def)

lemma prodag_elemfun:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); f \<in> carrier (prodag I A)\<rbrakk> \<Longrightarrow>
         f \<in> extensional I"
apply (simp add:prodag_carrier)
apply (simp add:carr_prodag_def)
done

lemma prodag_component:"\<lbrakk>f \<in> carrier (prodag I A); i \<in> I \<rbrakk> \<Longrightarrow>
                              f i \<in> carrier (A i)"
by (simp add:prodag_def carr_prodag_def)

lemma prodag_pOp:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  pop (prodag I A) = prod_pOp I A"
apply (simp add:prodag_def)
done

lemma prodag_iOp:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  mop (prodag I A) = prod_mOp I A"
apply (simp add:prodag_def)
done

lemma prodag_zero:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  zero (prodag I A) = prod_zero I A"
apply (simp add:prodag_def)
done

lemma prodag_sameTr0:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> Un_carrier I A = Un_carrier I B"
apply (simp add:Un_carrier_def)
done

lemma prodag_sameTr1:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> carr_prodag I A = carr_prodag I B"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (rule Pi_I)
 apply (subst Un_carrier_def, simp, blast)

apply (rule subsetI)
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (rule Pi_I)
 apply (subst Un_carrier_def, simp)
 apply blast
done

lemma prodag_sameTr2:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_pOp I A = prod_pOp I B"
apply (frule prodag_sameTr1 [of "I" "A" "B"], assumption+)
apply (simp add:prod_pOp_def)
apply (rule bivar_func_eq)
apply (rule ballI)+
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_sameTr3:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_mOp I A = prod_mOp I B"
apply (frule prodag_sameTr1 [of "I" "A" "B"], assumption+)
apply (simp add:prod_mOp_def)
apply (rule funcset_eq [of _ "carr_prodag I B"])
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI)
apply (rename_tac g) apply simp
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_sameTr4:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_zero I A = prod_zero I B"
apply (simp add:prod_zero_def)
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_same:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prodag I A = prodag I B"
apply (frule prodag_sameTr1, assumption+)
apply (frule prodag_sameTr2, assumption+)
apply (frule prodag_sameTr3, assumption+)
apply (frule prodag_sameTr4, assumption+)
apply (simp add:prodag_def)
done

lemma project_mem:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); j \<in> I; x \<in> carrier (prodag I A)\<rbrakk> \<Longrightarrow>
                         (PRoject I A j) x  \<in> carrier (A j)"
apply (simp add:PRoject_def)
apply (simp add:prodag_def)
apply (simp add:carr_prodag_def)
done

lemma project_aHom:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); j \<in> I\<rbrakk> \<Longrightarrow>
                         PRoject I A j \<in> aHom (prodag I A) (A j)"
apply (simp add:aHom_def)
apply (rule conjI)
 apply (simp add:project_mem)
apply (rule conjI)
 apply (simp add:PRoject_def restrict_def extensional_def)
 apply (rule allI, rule impI, simp add:prodag_def)
apply (rule ballI)+
 apply (simp add:prodag_def)
 apply (simp add:prod_pOp_def)
 apply (frule_tac X = a and Y = b in prod_pOp_mem[of I A], assumption+)
 apply (simp add:prod_pOp_def)
 apply (simp add:PRoject_def)
done

lemma project_aHom1:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                      \<forall>j \<in> I. PRoject I A j \<in> aHom (prodag I A) (A j)"
apply (rule ballI)
apply (rule project_aHom, assumption+)
done

definition
  A_to_prodag :: "[('a, 'm) aGroup_scheme, 'i set, 'i \<Rightarrow>('a \<Rightarrow> 'b),
   'i  \<Rightarrow> ('b, 'm1) aGroup_scheme] \<Rightarrow> ('a \<Rightarrow> ('i \<Rightarrow>'b))" where
 "A_to_prodag A I S B = (\<lambda>a\<in>carrier A. \<lambda>k\<in>I. S k a)"

 (* I is an index set, A is an abelian group, S: I \<rightarrow> carrier A \<rightarrow>
  carrier (prodag I B),   s i \<in> carrier A \<rightarrow> B i  *)

lemma A_to_prodag_mem:"\<lbrakk>aGroup A; \<forall>k\<in>I. aGroup (B k);  \<forall>k\<in>I. (S k) \<in>
 aHom A (B k); x \<in> carrier A \<rbrakk> \<Longrightarrow> A_to_prodag A I S B x \<in> carr_prodag I B"
apply (simp add:carr_prodag_def)
apply (rule conjI)
apply (simp add:A_to_prodag_def extensional_def restrict_def)
apply (simp add:Pi_def restrict_def A_to_prodag_def)
apply (rule conjI)
apply (rule allI) apply (rule impI)
apply (simp add:Un_carrier_def)
 apply (rotate_tac 2,
        frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (simp add:aHom_def) apply (erule conjE)+
 apply (frule_tac f = "S xa" and A = "carrier A" and B = "carrier (B xa)"
           and x = x in funcset_mem, assumption+)
 apply blast
apply (rule ballI)
 apply (rotate_tac 2,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (simp add:aHom_def) apply (erule conjE)+
 apply (simp add:Pi_def)
done

lemma A_to_prodag_aHom:"\<lbrakk>aGroup A; \<forall>k\<in>I. aGroup (B k); \<forall>k\<in>I. (S k) \<in>
 aHom A (B k) \<rbrakk>  \<Longrightarrow> A_to_prodag A I S B \<in> aHom A (a\<Pi>\<^bsub>I\<^esub> B)"
apply (simp add:aHom_def [of "A" "a\<Pi>\<^bsub>I\<^esub> B"])
apply (rule conjI)
 apply (simp add:prodag_def A_to_prodag_mem)

apply (rule conjI)
apply (simp add:A_to_prodag_def restrict_def extensional_def)
apply (rule ballI)+
 apply (frule_tac x = a and y = b in aGroup.ag_pOp_closed, assumption+)
 apply (frule_tac x = "a \<plusminus>\<^bsub>A\<^esub> b" in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule_tac x = a in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule_tac x = b in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule prodag_aGroup [of "I" "B"])
 apply (frule_tac x = a in A_to_prodag_mem[of "A" "I" "B" "S"], assumption+,
        frule_tac x = b in A_to_prodag_mem[of "A" "I" "B" "S"], assumption+,
        frule_tac x = "a \<plusminus>\<^bsub>A\<^esub> b" in A_to_prodag_mem[of "A" "I" "B" "S"],
                                                 assumption+)
 apply (frule prodag_aGroup[of "I" "B"],
        frule_tac x = "A_to_prodag A I S B a" and
 y = "A_to_prodag A I S B b" in aGroup.ag_pOp_closed [of "a\<Pi>\<^bsub>I\<^esub> B"])
 apply (simp add:prodag_carrier)
 apply (simp add:prodag_carrier)
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (simp add:prodag_carrier)
 apply (rule ballI)
 apply (simp add:A_to_prodag_def prod_pOp_def)
 apply (rotate_tac 2,
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (simp add:prodag_def prod_pOp_def)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (B k)")
apply (simp add: aHom_add)
done

definition
  finiteHom :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme, 'i \<Rightarrow> 'a] \<Rightarrow> bool" where
  "finiteHom I A f \<longleftrightarrow> f \<in> carr_prodag I A \<and> (\<exists>H. H \<subseteq> I \<and> finite H \<and> (
    \<forall>j \<in> (I - H). (f j) = \<zero>\<^bsub>(A j)\<^esub>))"

definition
  carr_dsumag :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> ('i  \<Rightarrow> 'a ) set" where
  "carr_dsumag I A = {f. finiteHom I A f}"

definition
  dsumag :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) aGroup" where
  "dsumag I A = \<lparr> carrier = carr_dsumag I A,
     pop = prod_pOp I A, mop = prod_mOp I A,
     zero = prod_zero I A\<rparr>"

definition
  dProj :: "['i set, 'i \<Rightarrow> ('a, 'more) aGroup_scheme, 'i]
                   \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "dProj I A x = (\<lambda>f\<in>carr_dsumag I A. f x)"

abbreviation
  DSUMag  ("(a\<Oplus>\<^bsub>_\<^esub> _)" [72,73]72) where
  "a\<Oplus>\<^bsub>I\<^esub> A == dsumag I A"

lemma dsum_pOp_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
    prod_pOp I A \<in> carr_dsumag I A \<rightarrow> carr_dsumag I A \<rightarrow> carr_dsumag I A"
apply (rule Pi_I)+
 apply (subst carr_dsumag_def) apply (simp add:CollectI)
apply (simp add:finiteHom_def)
 apply (rule conjI)
 apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
 apply (erule conjE)+ apply (simp add:prod_pOp_mem)
apply (simp add:carr_dsumag_def finiteHom_def) apply (erule conjE)+
 apply ((erule exE)+, (erule conjE)+)
 apply (frule_tac F = H and G = Ha in finite_UnI, assumption+)
 apply (subgoal_tac "\<forall>j\<in>I - (H \<union> Ha). prod_pOp I A x xa j = \<zero>\<^bsub>A j\<^esub>")
 apply (frule_tac A = H and B = Ha in Un_least[of _ "I"], assumption+)
  apply blast

 apply (rule ballI)
 apply (simp, (erule conjE)+)
 apply (frule_tac x = j in bspec, assumption,
         thin_tac "\<forall>k\<in>I. aGroup (A k)",
        frule_tac x = j in bspec, simp,
         thin_tac "\<forall>j\<in>I - H. x j = \<zero>\<^bsub>A j\<^esub>",
        frule_tac x = j in bspec, simp,
         thin_tac "\<forall>j\<in>I - Ha. xa j = \<zero>\<^bsub>A j\<^esub>")
 apply (simp add:prod_pOp_def)
 apply (rule aGroup.ag_l_zero) apply simp
 apply (rule aGroup.ex_zero) apply assumption
done

lemma dsum_pOp_mem:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); X \<in> carr_dsumag I A;
 Y \<in> carr_dsumag I A\<rbrakk> \<Longrightarrow> prod_pOp I A X Y \<in> carr_dsumag I A"
apply (frule dsum_pOp_func[of "I" "A"])
apply (frule funcset_mem[of "prod_pOp I A" "carr_dsumag I A"
              "carr_dsumag I A \<rightarrow> carr_dsumag I A" "X"], assumption+)
apply (rule funcset_mem[of "prod_pOp I A X" "carr_dsumag I A"
            "carr_dsumag I A" "Y"], assumption+)
done

lemma dsum_iOp_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  prod_mOp I A \<in> carr_dsumag I A \<rightarrow> carr_dsumag I A"
apply (rule Pi_I)
 apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
 apply (erule conjE)+ apply (simp add:prod_mOp_mem)
 apply (erule exE, (erule conjE)+)
 apply (simp add:prod_mOp_def)
 apply (subgoal_tac "\<forall>j\<in>I - H. -\<^sub>a\<^bsub>A j\<^esub> (x j) = \<zero>\<^bsub>A j\<^esub>")
 apply blast

apply (rule ballI)
 apply (frule_tac x = j in bspec, simp,
        thin_tac "\<forall>k\<in>I. aGroup (A k)",
        frule_tac x = j in bspec, simp,
        thin_tac "\<forall>j\<in>I - H. x j = \<zero>\<^bsub>A j\<^esub>", simp add:aGroup.ag_inv_zero)
done

lemma dsum_iOp_mem:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); X \<in> carr_dsumag I A\<rbrakk> \<Longrightarrow>
                         prod_mOp I A X \<in> carr_dsumag I A"
apply (frule dsum_iOp_func)
apply (simp add:Pi_def)
done

lemma dsum_zero_func:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                           prod_zero I A \<in> carr_dsumag I A"
apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
apply (rule conjI) apply (simp add:prod_zero_func)
 apply (subgoal_tac "{} \<subseteq> I") prefer 2 apply simp
 apply (subgoal_tac "finite {}") prefer 2 apply simp
 apply (subgoal_tac "\<forall>j\<in>I - {}. prod_zero I A j = \<zero>\<^bsub>A j\<^esub>")
 apply blast
 apply (rule ballI) apply simp
 apply (simp add:prod_zero_def)
done

lemma dsumag_sub_prodag:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                              carr_dsumag I A \<subseteq> carr_prodag I A"
by (rule subsetI,
       simp add:carr_dsumag_def finiteHom_def)

lemma carrier_dsumag:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
         carrier (dsumag I A) = carr_dsumag I A"
apply (simp add:dsumag_def)
done

lemma dsumag_elemfun:"\<lbrakk>\<forall>k\<in>I. aGroup (A k); f \<in> carrier (dsumag I A)\<rbrakk> \<Longrightarrow>
         f \<in> extensional I"
apply (simp add:carrier_dsumag)
apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
apply (erule conjE) apply (simp add:carr_prodag_def)
done

lemma dsumag_aGroup:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow> aGroup (dsumag I A)"
apply (simp add:aGroup_def [of "dsumag I A"])
apply (simp add:dsumag_def)
apply (simp add:dsum_pOp_func)
apply (simp add:dsum_iOp_func)
apply (simp add:dsum_zero_func)
apply (frule dsumag_sub_prodag[of "I" "A"])

apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (frule_tac X = a and Y = b in dsum_pOp_mem, assumption+)
 apply (frule_tac X = b and Y = c in dsum_pOp_mem, assumption+)
 apply (frule_tac X = "prod_pOp I A a b" and Y = c in dsum_pOp_mem,
                    assumption+)
 apply (frule_tac Y = "prod_pOp I A b c" and X = a in dsum_pOp_mem,
                    assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (simp add:subsetD) apply (simp add:subsetD)
 apply (rule ballI)
 apply (subst prod_pOp_mem_i, assumption+, (simp add:subsetD)+)
 apply (subst prod_pOp_mem_i, assumption+)
  apply (simp add:subsetD)+
 apply (subst prod_pOp_mem_i, assumption+, (simp add:subsetD)+)
 apply (subst prod_pOp_mem_i, assumption+) apply (simp add:subsetD)+
 apply (thin_tac "prod_pOp I A a b \<in> carr_dsumag I A",
        thin_tac "prod_pOp I A b c \<in> carr_dsumag I A",
        thin_tac "prod_pOp I A (prod_pOp I A a b) c \<in> carr_dsumag I A",
        thin_tac "prod_pOp I A a (prod_pOp I A b c) \<in> carr_dsumag I A",
        thin_tac "carr_dsumag I A \<subseteq> carr_prodag I A")

 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)",
        simp add:carr_dsumag_def finiteHom_def, (erule conjE)+,
        simp add:carr_prodag_def, (erule conjE)+)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>i\<in>I. a i \<in> carrier (A i)",
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>i\<in>I. b i \<in> carrier (A i)",
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>i\<in>I. c i \<in> carrier (A i)")
 apply (simp add:aGroup.aassoc)

apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
  apply (frule_tac X = a and Y = b in prod_pOp_mem[of "I" "A"],
         (simp add:subsetD)+)
  apply (frule_tac X = b and Y = a in prod_pOp_mem[of "I" "A"],
         (simp add:subsetD)+)
  apply (rule ballI,
         subst prod_pOp_mem_i, assumption+, (simp add:subsetD)+)
  apply (subst prod_pOp_mem_i, assumption+, (simp add:subsetD)+)
  apply (frule_tac x = l in bspec, assumption,
         thin_tac "\<forall>k\<in>I. aGroup (A k)")
  apply (frule_tac c = a in subsetD[of "carr_dsumag I A" "carr_prodag I A"],
          assumption+, thin_tac "a \<in> carr_dsumag I A",
         frule_tac c = b in subsetD[of "carr_dsumag I A" "carr_prodag I A"],
          assumption+, thin_tac "b \<in> carr_dsumag I A",
          thin_tac "carr_dsumag I A \<subseteq> carr_prodag I A")
  apply (simp add:carr_prodag_def, (erule conjE)+,
         simp add:aGroup.ag_pOp_commute)

apply (rule conjI)
 apply (rule allI, rule impI)
 apply (frule_tac X = a in prod_mOp_mem[of "I" "A"],
        simp add:subsetD)
 apply (frule_tac X = "prod_mOp I A a" and Y = a in prod_pOp_mem[of "I" "A"],
        simp add:subsetD, simp add:subsetD)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+,
        simp add:prod_zero_func)
 apply (rule ballI)
 apply (subst prod_pOp_mem_i, assumption+,
        simp add:subsetD, assumption)
 apply (subst prod_mOp_mem_i, assumption+, simp add:subsetD, assumption)
 apply (simp add:prod_zero_i)
 apply (frule_tac x = l in bspec, assumption,
         thin_tac "\<forall>k\<in>I. aGroup (A k)",
         thin_tac "prod_mOp I A a \<in> carr_prodag I A",
         thin_tac "prod_pOp I A (prod_mOp I A a) a \<in> carr_prodag I A",
        frule_tac c = a in subsetD[of "carr_dsumag I A" "carr_prodag I A"],
         assumption,
        thin_tac "carr_dsumag I A \<subseteq> carr_prodag I A",
        simp add:carr_prodag_def, (erule conjE)+)
  apply (frule_tac x = l in bspec, assumption,
         thin_tac "\<forall>i\<in>I. a i \<in> carrier (A i)")
  apply (rule aGroup.l_m, assumption+)

apply (rule allI, rule impI)
 apply (frule prod_zero_func[of "I" "A"])
 apply (frule_tac X = "prod_zero I A" and Y = a in prod_pOp_mem[of "I" "A"],
            assumption+, simp add:subsetD)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+,
        simp add:subsetD)
 apply (rule ballI)
 apply (subst prod_pOp_mem_i, assumption+)
        apply (simp add:subsetD, assumption)
 apply (simp add:prod_zero_i,
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. aGroup (A k)",
        frule_tac c = a in subsetD[of "carr_dsumag I A" "carr_prodag I A"],
                  assumption+,
        thin_tac "carr_dsumag I A \<subseteq> carr_prodag I A",
        thin_tac "a \<in> carr_dsumag I A",
        thin_tac "prod_pOp I A (prod_zero I A) a \<in> carr_prodag I A")
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (rule aGroup.l_zero, assumption)
 apply blast
done

lemma dsumag_pOp:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  pop (dsumag I A) = prod_pOp I A"
apply (simp add:dsumag_def)
done

lemma dsumag_mOp:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  mop (dsumag I A) = prod_mOp I A"
apply (simp add:dsumag_def)
done

lemma dsumag_zero:"\<forall>k\<in>I. aGroup (A k) \<Longrightarrow>
                  zero (dsumag I A) = prod_zero I A"
apply (simp add:dsumag_def)
done


subsection "Characterization of a direct product"

lemma direct_prod_mem_eq:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A);
       g \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A); \<forall>j\<in>I. (PRoject I A j) f = (PRoject I A j) g\<rbrakk> \<Longrightarrow>
       f = g"
apply (rule funcset_eq[of "f" "I" "g"])
 apply (thin_tac "\<forall>j\<in>I. aGroup (A j)",
        thin_tac "g \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A)",
        thin_tac "\<forall>j\<in>I. (\<pi>\<^bsub>I,A,j\<^esub>) f = (\<pi>\<^bsub>I,A,j\<^esub>) g",
        simp add:prodag_def carr_prodag_def)
  apply (thin_tac "\<forall>j\<in>I. aGroup (A j)",
        thin_tac "f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A)",
        thin_tac "\<forall>j\<in>I. (\<pi>\<^bsub>I,A,j\<^esub>) f = (\<pi>\<^bsub>I,A,j\<^esub>) g",
        simp add:prodag_def carr_prodag_def)
 apply (simp add:PRoject_def prodag_def)
done

lemma map_family_fun:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); aGroup S;
      \<forall>j\<in>I. ((g j) \<in> aHom S (A j)); x \<in> carrier S\<rbrakk> \<Longrightarrow>
         (\<lambda>y \<in> carrier S. (\<lambda>j\<in>I. (g j) y)) x \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A)"
apply (simp add:prodag_def carr_prodag_def)
 apply (simp add:aHom_mem)
 apply (rule Pi_I, simp add:Un_carrier_def)
 apply (frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>j\<in>I. aGroup (A j)",
        frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>j\<in>I. g j \<in> aHom S (A j)")
 apply (frule_tac G = "A xa" and f = "g xa" and a = x in aHom_mem[of "S"],
        assumption+, blast)
done

lemma map_family_aHom:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); aGroup S;
      \<forall>j\<in>I. ((g j) \<in> aHom S (A j))\<rbrakk> \<Longrightarrow>
         (\<lambda>y \<in> carrier S. (\<lambda>j\<in>I. (g j) y)) \<in> aHom S (a\<Pi>\<^bsub>I\<^esub> A)"
apply (subst aHom_def, simp)
 apply (simp add:aGroup.ag_pOp_closed)

apply (rule conjI)
 apply (rule Pi_I)
 apply (rule map_family_fun[of "I" "A" "S" "g"], assumption+)
apply (rule ballI)+
 apply (frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "S"],
                   assumption+)
 apply (frule_tac x = "a \<plusminus>\<^bsub>S\<^esub> b" in map_family_fun[of "I" "A" "S" "g"],
          assumption+, simp)
 apply (frule_tac x = a in map_family_fun[of "I" "A" "S" "g"],
          assumption+, simp,
         frule_tac x = b in map_family_fun[of "I" "A" "S" "g"],
          assumption+, simp)
 apply (frule prodag_aGroup[of "I" "A"])
 apply (frule_tac x = "(\<lambda>j\<in>I. g j a)" and y = "(\<lambda>j\<in>I. g j b)" in
        aGroup.ag_pOp_closed[of "a\<Pi>\<^bsub>I\<^esub> A"], assumption+)
 apply (simp only:prodag_carrier)

apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule ballI)
 apply (subst prodag_def, simp add:prod_pOp_def)
 apply (simp add:aHom_add)
done

lemma map_family_triangle:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); aGroup S;
         \<forall>j\<in>I. ((g j) \<in> aHom S (A j))\<rbrakk> \<Longrightarrow> \<exists>!f. f \<in> aHom S (a\<Pi>\<^bsub>I\<^esub> A) \<and>
                  (\<forall>j\<in>I. compos S (PRoject I A j) f =  (g j))"
apply (rule ex_ex1I)
apply (frule map_family_aHom[of "I" "A" "S" "g"], assumption+)
apply (subgoal_tac "\<forall>j\<in>I. compos S (\<pi>\<^bsub>I,A,j\<^esub>) (\<lambda>y\<in>carrier S. \<lambda>j\<in>I. g j y) = g j")
apply blast
apply (rule ballI)
apply (simp add:compos_def)
apply (rule funcset_eq[of _ "carrier S"])
 apply (simp add:compose_def) apply (simp add:aHom_def)
 apply (rule ballI)
 apply (frule prodag_aGroup[of "I" "A"])
 apply (frule prodag_carrier[of "I" "A"])
 apply (frule_tac f = "\<lambda>y\<in>carrier S. \<lambda>j\<in>I. g j y" and a = x in
        aHom_mem[of "S" "a\<Pi>\<^bsub>I\<^esub> A"], assumption+)
 apply (simp add:compose_def, simp add:PRoject_def)
apply (rename_tac f f1)
 apply (erule conjE)+
 apply (rule funcset_eq[of _ "carrier S"])
 apply (simp add:aHom_def, simp add:aHom_def)
 apply (rule ballI)
 apply (frule prodag_aGroup[of "I" "A"])
 apply (frule_tac f = f and a = x in aHom_mem[of "S" "a\<Pi>\<^bsub>I\<^esub> A"], assumption+,
        frule_tac f = f1 and a = x in aHom_mem[of "S" "a\<Pi>\<^bsub>I\<^esub> A"], assumption+)
 apply (rule_tac f = "f x" and g = "f1 x" in direct_prod_mem_eq[of "I" "A"],
        assumption+)
 apply (rule ballI)
 apply (rotate_tac 4,
        frule_tac x = j in bspec, assumption,
        thin_tac "\<forall>j\<in>I. compos S (\<pi>\<^bsub>I,A,j\<^esub>) f = g j",
         frule_tac x = j in bspec, assumption,
        thin_tac "\<forall>j\<in>I. compos S (\<pi>\<^bsub>I,A,j\<^esub>) f1 = g j",
        simp add:compos_def compose_def)
 apply (subgoal_tac "(\<lambda>x\<in>carrier S. (\<pi>\<^bsub>I,A,j\<^esub>) (f x)) x = g j x",
        subgoal_tac "(\<lambda>x\<in>carrier S. (\<pi>\<^bsub>I,A,j\<^esub>) (f1 x)) x = g j x",
        thin_tac "(\<lambda>x\<in>carrier S. (\<pi>\<^bsub>I,A,j\<^esub>) (f x)) = g j",
        thin_tac "(\<lambda>x\<in>carrier S. (\<pi>\<^bsub>I,A,j\<^esub>) (f1 x)) = g j",
simp+)
done

lemma Ag_ind_triangle:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); j \<in> I; f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) (B::'d set); j \<in> I\<rbrakk> \<Longrightarrow>
compos (a\<Pi>\<^bsub>I\<^esub> A) (compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)(PRoject I A j) (ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),
 (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)\<^esub> (Agii (a\<Pi>\<^bsub>I\<^esub> A) f))) (Agii (a\<Pi>\<^bsub>I\<^esub> A) f) =
                                       PRoject I A j"
apply (frule prodag_aGroup[of "I" "A"])
apply (frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (simp add:compos_def)
apply (rule funcset_eq[of _ "carrier (a\<Pi>\<^bsub>I\<^esub> A)"])
apply simp
apply (simp add:PRoject_def  prodag_carrier extensional_def)
apply (rule ballI)
apply (simp add:compose_def invfun_l)
apply (simp add:aGroup.Agii_mem)
apply (frule Ag_ind_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule_tac x = x in ainvf_l[of "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f"
                                     "Agii (a\<Pi>\<^bsub>I\<^esub> A) f"], assumption+)
apply simp
done

(** Note               f'
                 a\<Pi>\<^bsub>I\<^esub> A \<rightarrow> Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f
                     \     |
                      \    |
        PRoject I A j  \   | (PRoject I A j) o (f'\<inverse>\<^sup>1)
                        \  |
                          A j             , where f' = Agii (a\<Pi>\<^bsub>I\<^esub> A) f **)

definition
  ProjInd :: "['i set, 'i \<Rightarrow> ('a, 'm) aGroup_scheme, ('i \<Rightarrow> 'a) \<Rightarrow> 'd, 'i] \<Rightarrow>
                       ('d \<Rightarrow> 'a)" where
  "ProjInd I A f j = compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)(PRoject I A j) (ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A), (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)\<^esub> (Agii (a\<Pi>\<^bsub>I\<^esub> A) f))"

(** Note               f'
                 a\<Pi>\<^bsub>I\<^esub> A \<rightarrow> Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f
                     \     |
                      \    |
        PRoject I A j  \   | PRojInd I A f j
                        \  |
                          A j              **)

lemma ProjInd_aHom:"\<lbrakk>\<forall>j\<in> I. aGroup (A j); j \<in> I; f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) (B::'d set); j \<in> I\<rbrakk> \<Longrightarrow>
        (ProjInd I A f j) \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (A j)"
apply (frule prodag_aGroup[of "I" "A"])
apply (frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule_tac x = j in bspec, assumption)
apply (frule aGroup.Ag_ind_aHom[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (simp add:ProjInd_def)
apply (frule Ag_ind_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule ainvf_aHom[of "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "Agii (a\<Pi>\<^bsub>I\<^esub> A) f"],
             assumption+)
apply (frule project_aHom[of "I" "A" "j"], assumption)
apply (simp add:aHom_compos)
done

lemma ProjInd_aHom1:"\<lbrakk>\<forall>j\<in> I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) (B::'d set)\<rbrakk> \<Longrightarrow>
        \<forall>j\<in>I. (ProjInd I A f j) \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (A j)"
apply (rule ballI)
apply (simp add:ProjInd_aHom)
done

lemma ProjInd_mem_eq:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) B; aGroup S; x \<in> carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f);
      y \<in> carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f);
      \<forall>j\<in>I. (ProjInd I A f j x = ProjInd I A f j y)\<rbrakk> \<Longrightarrow> x = y"
apply (simp add:ProjInd_def)
apply (simp add:compos_def compose_def)
apply (frule prodag_aGroup[of "I" "A"])
apply (frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule aGroup.Ag_ind_aHom[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule Ag_ind_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule ainvf_aHom[of "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "Agii (a\<Pi>\<^bsub>I\<^esub> A) f"],
         assumption+)
apply (frule aHom_mem[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "a\<Pi>\<^bsub>I\<^esub> A" "ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f" "x"], assumption+,
       frule aHom_mem[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "a\<Pi>\<^bsub>I\<^esub> A" "ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f" "y"], assumption+)

apply (frule direct_prod_mem_eq[of "I" "A" "(ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f) x" "(ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f) y"], assumption+)
apply (thin_tac "ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f
     \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (a\<Pi>\<^bsub>I\<^esub> A)")
apply (frule ainvf_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "Agii (a\<Pi>\<^bsub>I\<^esub> A) f"],
                   assumption+)
apply (thin_tac "bijec\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f")
apply (unfold bijec_def, frule conjunct1, fold bijec_def)
apply (frule injec_inj_on[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "a\<Pi>\<^bsub>I\<^esub> A" "ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f"], assumption+)
apply (simp add:injective_iff[THEN sym, of "ainvf\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) f" "carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)" "x" "y"])
done

lemma ProjInd_mem_eq1:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) B; aGroup S;
      h \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f);
      \<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (ProjInd I A f j) h = ProjInd I A f j\<rbrakk>       \<Longrightarrow> h = ag_idmap (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)"
apply (rule funcset_eq[of _ "carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f)"])
 apply (simp add:aHom_def)
 apply (simp add:ag_idmap_def)
apply (rule ballI)
 apply (simp add:ag_idmap_def)
 apply (frule prodag_aGroup[of "I" "A"],
        frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
 apply (frule_tac a = x in aHom_mem[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f"
        "h"], assumption+)
 apply (rule_tac x = "h x" and y = x in ProjInd_mem_eq[of "I" "A" "f" "B" "S"],
        assumption+)
 apply (rotate_tac 1,
        rule ballI,
        frule_tac x = j in bspec, assumption,
        thin_tac "\<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) (ProjInd I A f j) h =
               ProjInd I A f j")
 apply (simp add:compos_def compose_def)
 apply (subgoal_tac "(\<lambda>x\<in>carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f). ProjInd I A f j (h x)) x
                    = ProjInd I A f j x",
        thin_tac "(\<lambda>x\<in>carrier (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f). ProjInd I A f j (h x)) =
           ProjInd I A f j")
 apply simp+
done

lemma Ag_ind_triangle1:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) (B::'d set); j \<in> I\<rbrakk> \<Longrightarrow>
      compos (a\<Pi>\<^bsub>I\<^esub> A) (ProjInd I A f j) (Agii (a\<Pi>\<^bsub>I\<^esub> A) f) =  PRoject I A j"
apply (simp add:ProjInd_def)
apply (simp add:Ag_ind_triangle)
done

lemma map_family_triangle1:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); f \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
      bij_to f (carrier (a\<Pi>\<^bsub>I\<^esub> A)) (B::'d set); aGroup S;
     \<forall>j\<in>I. ((g j) \<in> aHom S (A j))\<rbrakk> \<Longrightarrow> \<exists>!h. h \<in> aHom S (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f) \<and>
                  (\<forall>j\<in>I. compos S (ProjInd I A f j) h =  (g j))"
apply (frule prodag_aGroup[of "I" "A"])
apply (frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (frule Ag_ind_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" "f" "B"], assumption+)
apply (rule ex_ex1I)
apply (frule map_family_triangle[of "I" "A" "S" "g"], assumption+)
apply (frule ex1_implies_ex)
apply (erule exE)
apply (erule conjE)
apply (unfold bijec_def, frule conjunct2, fold bijec_def)
apply (unfold surjec_def, frule conjunct1, fold surjec_def)
apply (rename_tac fa,
       frule_tac f = fa in aHom_compos[of "S" "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f" _
                 "Agii (a\<Pi>\<^bsub>I\<^esub> A) f"], assumption+)
apply (subgoal_tac "\<forall>j\<in>I. compos S (ProjInd I A f j)
                           (compos S (Agii (a\<Pi>\<^bsub>I\<^esub> A) f) fa) = g j")
apply blast
apply (rule ballI)
apply (frule_tac N = "A j" and f = fa and g = "Agii (a\<Pi>\<^bsub>I\<^esub> A) f" and
 h = "ProjInd I A f j" in aHom_compos_assoc[of "S" "a\<Pi>\<^bsub>I\<^esub> A" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f"],
 assumption+) apply simp apply assumption+
apply (simp add:ProjInd_aHom)
apply simp
apply (thin_tac "compos S (ProjInd I A f j) (compos S (Agii (a\<Pi>\<^bsub>I\<^esub> A) f) fa) =
        compos S (compos (a\<Pi>\<^bsub>I\<^esub> A) (ProjInd I A f j) (Agii (a\<Pi>\<^bsub>I\<^esub> A) f)) fa")
apply (simp add:Ag_ind_triangle1)
apply (rename_tac h h1)
 apply (erule conjE)+
 apply (rule funcset_eq[of _ "carrier S"])
 apply (simp add:aHom_def, simp add:aHom_def)
 apply (rule ballI)
 apply (simp add:compos_def)

apply (frule_tac f = h and a = x in aHom_mem[of "S" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f"],
          assumption+,
       frule_tac f = h1 and a = x in aHom_mem[of "S" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) f"],
          assumption+)
apply (rule_tac x = "h x" and y = "h1 x" in ProjInd_mem_eq[of "I" "A" "f"
       "B" "S"], assumption+)
apply (rule ballI)
apply (rotate_tac 5,
       frule_tac x = j in bspec, assumption,
       thin_tac "\<forall>j\<in>I. compose (carrier S) (ProjInd I A f j) h = g j",
       frule_tac x = j in bspec, assumption,
       thin_tac "\<forall>j\<in>I. compose (carrier S) (ProjInd I A f j) h1 = g j")
apply (simp add:compose_def,
       subgoal_tac "(\<lambda>x\<in>carrier S. ProjInd I A f j (h x)) x = g j x",
       thin_tac "(\<lambda>x\<in>carrier S. ProjInd I A f j (h x)) = g j",
       subgoal_tac "(\<lambda>x\<in>carrier S. ProjInd I A f j (h1 x)) x = g j x",
       thin_tac "(\<lambda>x\<in>carrier S. ProjInd I A f j (h1 x)) = g j", simp+)
done

lemma  map_family_triangle2:"\<lbrakk>I \<noteq> {}; \<forall>j\<in>I. aGroup (A j); aGroup S;
       \<forall>j\<in>I. g j \<in> aHom S (A j); ff \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
        bij_to ff (carrier (a\<Pi>\<^bsub>I\<^esub> A)) B;
        h1 \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) S;
        \<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (g j) h1 = ProjInd I A ff j;
        h2 \<in> aHom S (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff);
        \<forall>j\<in>I. compos S (ProjInd I A ff j) h2 = g j\<rbrakk>
       \<Longrightarrow> \<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (ProjInd I A ff j)
                 (compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) h2 h1) =
                ProjInd I A ff j"
apply (rule ballI)
apply (frule prodag_aGroup[of "I" "A"])
apply (frule_tac f = ff in aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" _ "B"], assumption+)

apply (frule_tac N = "A j" and h = "ProjInd I A ff j" in aHom_compos_assoc[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" "S" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" _ "h1" "h2"], assumption+)
 apply simp apply assumption+ apply (simp add:ProjInd_aHom)
apply simp
done

lemma  map_family_triangle3:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); aGroup S; aGroup S1;
       \<forall>j\<in>I. f j \<in> aHom S (A j); \<forall>j\<in>I. g j \<in> aHom S1 (A j);
        h1 \<in> aHom S1 S; h2 \<in> aHom S S1;
        \<forall>j\<in>I. compos S (g j) h2 = f j;
        \<forall>j\<in>I. compos S1 (f j) h1 = g j\<rbrakk>
       \<Longrightarrow> \<forall>j\<in>I. compos S (f j) (compos S h1 h2) = f j"
apply (rule ballI)
apply (frule_tac h = "f j" and N = "A j" in aHom_compos_assoc[of "S" "S1"
                              "S" _ "h2" "h1"], assumption+)
apply simp apply assumption+ apply simp
apply simp
done

lemma map_family_triangle4:"\<lbrakk>\<forall>j\<in>I. aGroup (A j); aGroup S;
                \<forall>j\<in>I. f j \<in> aHom S (A j)\<rbrakk> \<Longrightarrow>
               \<forall>j\<in>I. compos S (f j) (ag_idmap S) = f j"
apply (rule ballI)
apply (frule_tac x = j in bspec, assumption,
       thin_tac "\<forall>j\<in>I. aGroup (A j)",
       frule_tac x = j in bspec, assumption,
       thin_tac "\<forall>j\<in>I. f j \<in> aHom S (A j)")
apply (simp add:compos_aI_r)
done

lemma  prod_triangle:"\<lbrakk>I \<noteq> {}; \<forall>j\<in>I. aGroup (A j); aGroup S;
       \<forall>j\<in>I. g j \<in> aHom S (A j); ff \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> B;
        bij_to ff (carrier (a\<Pi>\<^bsub>I\<^esub> A)) B;
        h1 \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) S;
        \<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (g j) h1 = ProjInd I A ff j;
        h2 \<in> aHom S (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff);
        \<forall>j\<in>I. compos S (ProjInd I A ff j) h2 = g j\<rbrakk>
       \<Longrightarrow> (compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) h2 h1) = ag_idmap (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff)"
apply (frule map_family_triangle2[of "I" "A" "S" "g" "ff" "B" "h1" "h2"], assumption+)
apply (frule prodag_aGroup[of "I" "A"],
       frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" "ff" "B"], assumption+)
apply (frule aHom_compos[of "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" "S" "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" "h1"
                            "h2"], assumption+)
apply (rule ProjInd_mem_eq1[of "I" "A" "ff" "B" "S"
                            "compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) h2 h1"], assumption+)
done

lemma characterization_prodag:"\<lbrakk>I \<noteq> {}; \<forall>j\<in>(I::'i set). aGroup ((A j)::
    ('a, 'm) aGroup_scheme); aGroup (S::'d aGroup);
    \<forall>j\<in>I. ((g j) \<in> aHom S (A j)); \<exists>ff. ff \<in> carrier (a\<Pi>\<^bsub>I\<^esub> A) \<rightarrow> (B::'d set) \<and>
          bij_to ff (carrier (a\<Pi>\<^bsub>I\<^esub> A)) B;
    \<forall>(S':: 'd aGroup). aGroup S' \<longrightarrow>
        (\<forall>g'. (\<forall>j\<in>I. (g' j) \<in> aHom S' (A j) \<longrightarrow>
         (\<exists>! f. f \<in> aHom S' S \<and> (\<forall>j\<in>I. compos S' (g j) f =  (g' j)))))\<rbrakk> \<Longrightarrow>
     \<exists>h. bijec\<^bsub>(prodag I A),S\<^esub> h"
apply (frule prodag_aGroup[of "I" "A"])
apply (erule exE)
apply (frule_tac f = ff in aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" _ "B"], erule conjE,
       assumption, simp, erule conjE)
apply (frule aGroup.Ag_ind_aGroup[of "a\<Pi>\<^bsub>I\<^esub> A" _ "B"], assumption+,
       frule_tac a = S in forall_spec, assumption+)
apply (rotate_tac -1,
       frule_tac x = g in spec,
       thin_tac "\<forall>g'. \<forall>j\<in>I. g' j \<in> aHom S (A j) \<longrightarrow>
              (\<exists>!f. f \<in> aHom S S \<and> (\<forall>j\<in>I. compos S (g j) f = g' j))")
apply (frule_tac a = "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" in forall_spec, assumption+,
       thin_tac "\<forall>S'. aGroup S' \<longrightarrow> (\<forall>g'. \<forall>j\<in>I. g' j \<in> aHom S' (A j) \<longrightarrow>
                (\<exists>!f. f \<in> aHom S' S \<and> (\<forall>j\<in>I. compos S' (g j) f = g' j)))")
apply (frule_tac x = "ProjInd I A ff" in spec,
       thin_tac "\<forall>g'. \<forall>j\<in>I. g' j \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (A j) \<longrightarrow>
                     (\<exists>!f. f \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) S \<and>
                          (\<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (g j) f =
                                 g' j))")
apply (frule_tac f = ff in ProjInd_aHom1[of "I" "A" _ "B"], assumption+)
apply (simp add:nonempty_ex[of "I"],
       rotate_tac -2,
       frule ex1_implies_ex,
       thin_tac "\<exists>!f. f \<in> aHom (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) S \<and>
         (\<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (g j) f = ProjInd I A ff j)",
       rotate_tac -1, erule exE, erule conjE)
apply (rename_tac ff h1,
       frule_tac f = ff in map_family_triangle1[of "I" "A" _  "B" "S" "g"],
           assumption+,
       rotate_tac -1,
       frule ex1_implies_ex,
       thin_tac "\<exists>!h. h \<in> aHom S (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) \<and>
             (\<forall>j\<in>I. compos S (ProjInd I A ff j) h = g j)",
       rotate_tac -1,
       erule exE, erule conjE)
apply (rename_tac ff h1 h2)
apply (frule_tac ff = ff and ?h1.0 = h1 and ?h2.0 = h2 in prod_triangle[of "I"
        "A" "S" "g" _ "B"], assumption+,
       frule_tac ?S1.0 = "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" in map_family_triangle3[of "I"
                "A" "S" _ "g"],
        assumption+,
       frule_tac f = h2 and g = h1 and M =  "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" in
                aHom_compos[of "S" _ "S" ], assumption+)
apply (erule ex1E)
 apply (rotate_tac -1,
        frule_tac x = "compos S h1 h2" in spec,
        frule map_family_triangle4[of "I" "A" "S" "g"], assumption+,
        frule aGroup.aI_aHom[of "S"])
 apply (frule_tac x = "aI\<^bsub>S\<^esub>" in spec,
   thin_tac "\<forall>y. y \<in> aHom S S \<and> (\<forall>j\<in>I. compos S (g j) y = g j) \<longrightarrow> y = f",
   simp,
   thin_tac "\<forall>j\<in>I. compos S (ProjInd I A ff j) h2 = g j",
   thin_tac "\<forall>j\<in>I. compos S (g j) f = g j",
   thin_tac "\<forall>j\<in>I. compos (Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff) (g j) h1 = ProjInd I A ff j")
 apply (rotate_tac -1, frule sym, thin_tac "aI\<^bsub>S\<^esub> = f", simp,
        frule_tac A = "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" and f = h1 and g = h2 in
         compos_aI_inj[of _ "S"], assumption+,
        frule_tac B = "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" and f = h2 and g = h1 in
         compos_aI_surj[of "S"], assumption+)
 apply (frule_tac f = ff in Ag_ind_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" _ "B"], assumption+,
        frule_tac F = "Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff" and f = "Agii (a\<Pi>\<^bsub>I\<^esub> A) ff" and g = h1
           in compos_bijec[of "a\<Pi>\<^bsub>I\<^esub> A" _ "S"], assumption+)
apply (subst bijec_def, simp)
 apply (thin_tac "bijec\<^bsub>(a\<Pi>\<^bsub>I\<^esub> A),Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff\<^esub> Agii (a\<Pi>\<^bsub>I\<^esub> A) ff",
        thin_tac "injec\<^bsub>Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff,S\<^esub> h1",
        thin_tac "surjec\<^bsub>Ag_ind (a\<Pi>\<^bsub>I\<^esub> A) ff,S\<^esub> h1")
apply (rule exI, simp)
done

(***  Note.
                                     f
                                  S' \<rightarrow> S
                                    \   |
                                 g' j\  | g j
                                      \ |
                                        A j

       ***)



chapter "Ring theory"

section "Definition of a ring and an ideal"

record 'a Ring = "'a aGroup" +
  tp ::  "['a, 'a ] \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>r\<index>" 70)
  un :: "'a"   ("1\<^sub>r\<index>")

locale Ring =
 fixes R (structure)

 assumes
         pop_closed: "pop R \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R"
 and     pop_aassoc : "\<lbrakk>a \<in> carrier R; b \<in> carrier R; c \<in> carrier R\<rbrakk> \<Longrightarrow>
         (a \<plusminus> b) \<plusminus> c = a \<plusminus> (b \<plusminus> c)"
 and     pop_commute:"\<lbrakk>a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow> a \<plusminus> b = b \<plusminus> a"
 and     mop_closed:"mop R \<in> carrier R \<rightarrow> carrier R"
 and     l_m :"a \<in> carrier R \<Longrightarrow>  (-\<^sub>a a) \<plusminus> a = \<zero>"
 and     ex_zero: "\<zero> \<in> carrier R"
 and     l_zero:"a \<in> carrier R \<Longrightarrow> \<zero> \<plusminus> a = a"
 and     tp_closed: "tp R \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R"
 and     tp_assoc : "\<lbrakk>a \<in> carrier R; b \<in> carrier R; c \<in> carrier R\<rbrakk> \<Longrightarrow>
                  (a \<cdot>\<^sub>r b) \<cdot>\<^sub>r c = a \<cdot>\<^sub>r (b \<cdot>\<^sub>r c)"
 and     tp_commute: "\<lbrakk>a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>r b = b  \<cdot>\<^sub>r a"
 and     un_closed: "(1\<^sub>r) \<in> carrier R"
 and     rg_distrib: "\<lbrakk>a \<in> carrier R; b \<in> carrier R; c \<in> carrier R\<rbrakk> \<Longrightarrow>
                     a \<cdot>\<^sub>r (b \<plusminus> c) = a \<cdot>\<^sub>r b  \<plusminus>  a \<cdot>\<^sub>r c"
 and     rg_l_unit: "a \<in> carrier R \<Longrightarrow> (1\<^sub>r) \<cdot>\<^sub>r a = a"

definition
  zeroring :: "('a, 'more) Ring_scheme \<Rightarrow> bool" where
  "zeroring R \<longleftrightarrow> Ring R \<and> carrier R = {\<zero>\<^bsub>R\<^esub>}"

primrec nscal ::  "('a, 'more) Ring_scheme  => 'a => nat  => 'a"
where
  nscal_0:  "nscal R x 0 = \<zero>\<^bsub>R\<^esub>"
| nscal_suc:  "nscal R x (Suc n) = (nscal R x n) \<plusminus>\<^bsub>R\<^esub> x"

primrec npow ::  "('a, 'more) Ring_scheme  => 'a => nat  => 'a"
where
  npow_0: "npow R x 0 = 1\<^sub>r\<^bsub>R\<^esub>"
| npow_suc: "npow R x (Suc n) = (npow R x n) \<cdot>\<^sub>r\<^bsub>R\<^esub> x"

primrec nprod  :: "('a, 'more) Ring_scheme => (nat => 'a) => nat => 'a"
where
  nprod_0: "nprod R f 0 = f 0"
| nprod_suc: "nprod R f (Suc n) = (nprod R f n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (f (Suc n))"

primrec nsum :: "('a, 'more) aGroup_scheme => (nat => 'a) => nat => 'a"
where
  nsum_0: "nsum R f 0 = f 0"
| nsum_suc: "nsum R f (Suc n) = (nsum R f n) \<plusminus>\<^bsub>R\<^esub> (f (Suc n))"

abbreviation
  NSCAL :: "[nat, ('a, 'more) Ring_scheme, 'a] \<Rightarrow> 'a"
    ("(3 _ \<times>\<^bsub>_\<^esub> _)" [75,75,76]75) where
  "n \<times>\<^bsub>R\<^esub> x == nscal R x n"

abbreviation
  NPOW :: "['a, ('a, 'more) Ring_scheme, nat] \<Rightarrow>  'a"
    ("(3_^\<^bsup>_ _\<^esup>)" [77,77,78]77) where
  "a^\<^bsup>R n\<^esup> == npow R a n"

abbreviation
  SUM :: "('a, 'more) aGroup_scheme => (nat => 'a) => nat => 'a"
    ("(3\<Sigma>\<^sub>e _ _ _)" [85,85,86]85) where
  "\<Sigma>\<^sub>e G f n == nsum G f n"

abbreviation
  NPROD :: "[('a, 'm) Ring_scheme, nat, nat \<Rightarrow> 'a] \<Rightarrow> 'a"
    ("(3e\<Pi>\<^bsub>_,_\<^esub> _)" [98,98,99]98) where
  "e\<Pi>\<^bsub>R,n\<^esub> f == nprod R f n"

definition
  fSum :: "[_, (nat => 'a), nat, nat] \<Rightarrow> 'a" where
  "fSum A f n m = (if n \<le> m then nsum A (cmp f (slide n))(m - n)
                       else \<zero>\<^bsub>A\<^esub>)"

abbreviation
  FSUM :: "[('a, 'more) aGroup_scheme, (nat \<Rightarrow> 'a), nat, nat] \<Rightarrow> 'a"
    ("(4\<Sigma>\<^sub>f _ _ _ _)" [85,85,85,86]85) where
  "\<Sigma>\<^sub>f G f n m == fSum G f n m"

lemma (in aGroup) nsum_zeroGTr:"(\<forall>j \<le> n. f j = \<zero>) \<longrightarrow> nsum A f n = \<zero>"
apply (induct_tac n)
 apply (rule impI, simp)

apply (rule impI)
apply (cut_tac n = n in Nsetn_sub_mem1, simp)
apply (cut_tac ex_zero)
apply (simp add:l_zero[of \<zero>])
done

lemma (in aGroup) nsum_zeroA:"\<forall>j \<le> n. f j = \<zero> \<Longrightarrow>   nsum A f n = \<zero>"
apply (simp add:nsum_zeroGTr)
done

definition
  sr :: "[_ , 'a set] \<Rightarrow> bool" where
  "sr R S == S \<subseteq> carrier R \<and> 1\<^sub>r\<^bsub>R\<^esub> \<in> S \<and> (\<forall>x\<in>S. \<forall>y \<in> S. x  \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> y) \<in> S \<and>
               x \<cdot>\<^sub>r\<^bsub>R\<^esub> y \<in> S)"

definition
  Sr :: "[_ , 'a set] \<Rightarrow> _" where
  "Sr R S = R \<lparr>carrier := S, pop := \<lambda>x\<in>S. \<lambda>y\<in>S. x \<plusminus>\<^bsub>R\<^esub> y, mop := \<lambda>x\<in>S. (-\<^sub>a\<^bsub>R\<^esub> x),
    zero := \<zero>\<^bsub>R\<^esub>, tp := \<lambda>x\<in>S. \<lambda>y\<in>S. x \<cdot>\<^sub>r\<^bsub>R\<^esub> y, un := 1\<^sub>r\<^bsub>R\<^esub> \<rparr>"

(** sr is a subring without ring structure, Sr is a subring with Ring structure
     **)


lemma (in Ring) Ring: "Ring R" ..

lemma (in Ring) ring_is_ag:"aGroup R"
apply (rule aGroup.intro,
       rule pop_closed,
       rule pop_aassoc, assumption+,
       rule pop_commute, assumption+,
       rule mop_closed,
       rule l_m, assumption,
       rule ex_zero,
       rule l_zero, assumption)
done

lemma (in Ring) ring_zero:"\<zero> \<in> carrier R"
by (simp add: ex_zero)

lemma (in Ring) ring_one:"1\<^sub>r \<in> carrier R"
by (simp add:un_closed)

lemma (in Ring) ring_tOp_closed:"\<lbrakk> x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow>
                     x \<cdot>\<^sub>r y \<in> carrier R"
apply (cut_tac tp_closed)
 apply (frule funcset_mem[of "(\<cdot>\<^sub>r)" "carrier R" "carrier R \<rightarrow> carrier R"
            "x"], assumption+,
        thin_tac "(\<cdot>\<^sub>r) \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R")
 apply (rule funcset_mem[of "(\<cdot>\<^sub>r) x" "carrier R" "carrier R" "y"],
              assumption+)
done

lemma (in Ring) ring_tOp_commute:"\<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow>
                x \<cdot>\<^sub>r y = y \<cdot>\<^sub>r x"
by (simp add:tp_commute)

lemma (in Ring) ring_distrib1:"\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk>
                 \<Longrightarrow> x \<cdot>\<^sub>r (y \<plusminus> z) = x \<cdot>\<^sub>r y \<plusminus> x \<cdot>\<^sub>r z"
by (simp add:rg_distrib)

lemma (in Ring) ring_distrib2:"\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk>
                \<Longrightarrow> (y \<plusminus> z) \<cdot>\<^sub>r x = y \<cdot>\<^sub>r x \<plusminus>  z \<cdot>\<^sub>r x"
apply (subst tp_commute[of "y \<plusminus> z" "x"])
 apply (cut_tac ring_is_ag, simp add:aGroup.ag_pOp_closed)
 apply assumption
apply (subst ring_distrib1, assumption+)
 apply (simp add:tp_commute)
done

lemma (in Ring) ring_distrib3:"\<lbrakk>a \<in> carrier R; b \<in> carrier R; x \<in> carrier R;
      y \<in> carrier R \<rbrakk> \<Longrightarrow> (a \<plusminus> b) \<cdot>\<^sub>r (x \<plusminus> y) =
                                          a \<cdot>\<^sub>r x \<plusminus> a \<cdot>\<^sub>r y \<plusminus> b \<cdot>\<^sub>r x \<plusminus> b \<cdot>\<^sub>r y"
apply (subst ring_distrib2)+
 apply (cut_tac ring_is_ag)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply ((subst ring_distrib1)+, assumption+)
 apply (subst ring_distrib1, assumption+)
 apply (rule pop_aassoc [THEN sym, of "a \<cdot>\<^sub>r x \<plusminus> a \<cdot>\<^sub>r y" "b \<cdot>\<^sub>r x" "b \<cdot>\<^sub>r y"])
 apply (cut_tac ring_is_ag, rule aGroup.ag_pOp_closed, assumption)
 apply (simp add:ring_tOp_closed)+
done

lemma (in Ring) rEQMulR:
  "\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; x = y \<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r z = y \<cdot>\<^sub>r z"
by simp

lemma (in Ring) ring_tOp_assoc:"\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk>
 \<Longrightarrow> (x \<cdot>\<^sub>r y) \<cdot>\<^sub>r z = x \<cdot>\<^sub>r (y \<cdot>\<^sub>r z)"
by (simp add:tp_assoc)

lemma (in Ring) ring_l_one:"x \<in> carrier R \<Longrightarrow> 1\<^sub>r \<cdot>\<^sub>r x = x"
by (simp add:rg_l_unit)

lemma (in Ring) ring_r_one:"x \<in> carrier R  \<Longrightarrow> x \<cdot>\<^sub>r 1\<^sub>r = x"
 apply (subst ring_tOp_commute, assumption+)
 apply (simp add:un_closed)
 apply (simp add:ring_l_one)
done

lemma (in Ring) ring_times_0_x:"x \<in> carrier R \<Longrightarrow> \<zero> \<cdot>\<^sub>r x = \<zero>"
apply (cut_tac ring_is_ag)
apply (cut_tac ring_zero)
apply (frule ring_distrib2 [of "x" "\<zero>" "\<zero>"], assumption+)
apply (simp add:aGroup.ag_l_zero [of "R" "\<zero>"])
apply (frule ring_tOp_closed [of "\<zero>" "x"], assumption+)
apply (frule sym, thin_tac "\<zero> \<cdot>\<^sub>r x = \<zero> \<cdot>\<^sub>r x \<plusminus> \<zero> \<cdot>\<^sub>r x")
apply (frule aGroup.ag_eq_sol2 [of "R" "\<zero> \<cdot>\<^sub>r x" "\<zero> \<cdot>\<^sub>r x" "\<zero> \<cdot>\<^sub>r x"],
        assumption+)
apply (thin_tac "\<zero> \<cdot>\<^sub>r x \<plusminus> \<zero> \<cdot>\<^sub>r x = \<zero> \<cdot>\<^sub>r x")
apply (simp add:aGroup.ag_r_inv1)
done

lemma (in Ring) ring_times_x_0:"x \<in> carrier R \<Longrightarrow>  x \<cdot>\<^sub>r \<zero> = \<zero>"
apply (cut_tac ring_zero)
apply (subst ring_tOp_commute, assumption+, simp add:ring_zero)
apply (simp add:ring_times_0_x)
done

lemma (in Ring) rMulZeroDiv:
     "\<lbrakk> x \<in> carrier R; y \<in> carrier R; x = \<zero> \<or> y = \<zero> \<rbrakk> \<Longrightarrow> x  \<cdot>\<^sub>r  y = \<zero>"
apply (erule disjE, simp)
apply (rule ring_times_0_x, assumption+)
apply (simp, rule ring_times_x_0, assumption+)
done

lemma (in Ring) ring_inv1:"\<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
      -\<^sub>a (a \<cdot>\<^sub>r b) = (-\<^sub>a a) \<cdot>\<^sub>r b \<and> -\<^sub>a (a \<cdot>\<^sub>r b) = a \<cdot>\<^sub>r (-\<^sub>a b)"
apply (cut_tac ring_is_ag)
apply (rule conjI)
apply (frule ring_distrib2 [THEN sym, of "b" "a" "-\<^sub>a a"], assumption+)
 apply (frule aGroup.ag_mOp_closed [of "R" "a"], assumption+)
 apply (simp add:aGroup.ag_r_inv1 [of "R" "a"])
 apply (simp add:ring_times_0_x)
 apply (frule aGroup.ag_mOp_closed [of "R" "a"], assumption+)
 apply (frule ring_tOp_closed [of "a" "b"], assumption+)
 apply (frule ring_tOp_closed [of "-\<^sub>a a" "b"], assumption+)
 apply (frule aGroup.ag_eq_sol1 [of "R" "a \<cdot>\<^sub>r b" "(-\<^sub>a a) \<cdot>\<^sub>r b" "\<zero>"],
           assumption+)
 apply (rule ring_zero, assumption+)
 apply (thin_tac "a \<cdot>\<^sub>r b \<plusminus> (-\<^sub>a a) \<cdot>\<^sub>r b = \<zero>")
 apply (frule sym) apply (thin_tac "(-\<^sub>a a) \<cdot>\<^sub>r b = -\<^sub>a (a \<cdot>\<^sub>r b) \<plusminus> \<zero>")
 apply (frule aGroup.ag_mOp_closed [of "R" " a \<cdot>\<^sub>r b"], assumption+)
 apply (simp add:aGroup.ag_r_zero)
apply (frule ring_distrib1 [THEN sym, of "a" "b" "-\<^sub>a b"], assumption+)
 apply (simp add:aGroup.ag_mOp_closed)
  apply (simp add:aGroup.ag_r_inv1 [of "R" "b"])
  apply (simp add:ring_times_x_0)
 apply (frule aGroup.ag_mOp_closed [of "R" "b"], assumption+)
 apply (frule ring_tOp_closed [of "a" "b"], assumption+)
 apply (frule ring_tOp_closed [of "a" "-\<^sub>a b"], assumption+)
 apply (frule aGroup.ag_eq_sol1 [THEN sym, of "R" "a \<cdot>\<^sub>r b" "a \<cdot>\<^sub>r (-\<^sub>a b)" "\<zero>"],
                                                      assumption+)
 apply (simp add:ring_zero) apply assumption
 apply (frule aGroup.ag_mOp_closed [of "R" " a \<cdot>\<^sub>r b"], assumption+)
  apply (simp add:aGroup.ag_r_zero)
done

lemma (in Ring) ring_inv1_1:"\<lbrakk>a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
      -\<^sub>a (a \<cdot>\<^sub>r b) = (-\<^sub>a a) \<cdot>\<^sub>r b"
apply (simp add:ring_inv1)
done

lemma (in Ring) ring_inv1_2:"\<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
                                -\<^sub>a (a \<cdot>\<^sub>r b) = a \<cdot>\<^sub>r (-\<^sub>a b)"
apply (frule ring_inv1 [of "a" "b"], assumption+)
apply (frule conjunct2)
apply (thin_tac "-\<^sub>a a \<cdot>\<^sub>r b = (-\<^sub>a a) \<cdot>\<^sub>r b \<and> -\<^sub>a (a \<cdot>\<^sub>r b) = a \<cdot>\<^sub>r (-\<^sub>a b)")
apply simp
done

lemma (in Ring) ring_times_minusl:"a \<in> carrier R \<Longrightarrow>  -\<^sub>a a = (-\<^sub>a 1\<^sub>r) \<cdot>\<^sub>r a"
apply (cut_tac ring_one)
apply (frule ring_inv1_1[of "1\<^sub>r" "a"], assumption+)
apply (simp add:ring_l_one)
done

lemma (in Ring) ring_times_minusr:"a \<in> carrier R \<Longrightarrow>  -\<^sub>a a = a \<cdot>\<^sub>r (-\<^sub>a 1\<^sub>r)"
apply (cut_tac ring_one)
apply (frule ring_inv1_2[of "a" "1\<^sub>r"], assumption+)
apply (simp add:ring_r_one)
done

lemma (in Ring) ring_inv1_3:"\<lbrakk>a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
                           a \<cdot>\<^sub>r b = (-\<^sub>a a) \<cdot>\<^sub>r (-\<^sub>a b)"
apply (cut_tac ring_is_ag)
apply (subst  aGroup.ag_inv_inv[THEN sym], assumption+)
apply (frule aGroup.ag_mOp_closed[of "R" "a"], assumption+)
apply (subst ring_inv1_1[THEN sym, of "-\<^sub>a a" "b"], assumption+)
apply (subst ring_inv1_2[of "-\<^sub>a a" "b"], assumption+, simp)
done

lemma (in Ring) ring_distrib4:"\<lbrakk>a \<in> carrier R; b \<in> carrier R;
                                x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
      a \<cdot>\<^sub>r b \<plusminus> (-\<^sub>a x \<cdot>\<^sub>r y) = a \<cdot>\<^sub>r (b \<plusminus> (-\<^sub>a y)) \<plusminus> (a \<plusminus> (-\<^sub>a x)) \<cdot>\<^sub>r y"
apply (cut_tac ring_is_ag)
apply (subst ring_distrib1, assumption+)
apply (rule aGroup.ag_mOp_closed, assumption+)
apply (subst ring_distrib2, assumption+)
apply (rule aGroup.ag_mOp_closed, assumption+)
apply (subst aGroup.pOp_assocTr43, assumption+)
apply (rule ring_tOp_closed, assumption+)+
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ring_tOp_closed)
 apply (simp add:aGroup.ag_mOp_closed)+
apply (subst ring_distrib1 [THEN sym, of "a" _], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
apply (simp add:aGroup.ag_l_inv1)
apply (simp add:ring_times_x_0)
apply (subst aGroup.ag_r_zero, assumption+)
apply (simp add:ring_tOp_closed)
apply (simp add: ring_inv1_1)
done

lemma (in Ring) rMulLC:
     "\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r (y \<cdot>\<^sub>r z) = y \<cdot>\<^sub>r (x \<cdot>\<^sub>r z)"
  apply (subst ring_tOp_assoc [THEN sym], assumption+)
  apply (subst ring_tOp_commute [of "x" "y"], assumption+)
  apply (subst ring_tOp_assoc, assumption+)
  apply simp
  done

lemma (in Ring) Zero_ring:"1\<^sub>r = \<zero> \<Longrightarrow> zeroring R"
apply (simp add:zeroring_def)
apply (rule conjI)
 apply (rule Ring_axioms)
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac x = x in ring_r_one, simp add:ring_times_x_0)

 apply (simp add:ring_zero)
done

lemma (in Ring) Zero_ring1:"\<not> (zeroring R) \<Longrightarrow>  1\<^sub>r \<noteq> \<zero>"
apply (rule contrapos_pp, simp+,
       cut_tac Zero_ring, simp+)
done

lemma (in Ring) Sr_one:"sr R S \<Longrightarrow> 1\<^sub>r \<in> S"
apply (simp add:sr_def)
done

lemma (in Ring) Sr_zero:"sr R S \<Longrightarrow> \<zero> \<in> S"
apply (cut_tac ring_is_ag, frule Sr_one[of "S"])
apply (simp add:sr_def) apply (erule conjE)+
apply (frule_tac x = "1\<^sub>r" in bspec, assumption,
       thin_tac "\<forall>x\<in>S. \<forall>y\<in>S. x \<plusminus> -\<^sub>a y \<in> S \<and> x \<cdot>\<^sub>r y \<in> S",
       frule_tac x = "1\<^sub>r" in bspec, assumption,
       thin_tac "\<forall>y\<in>S. 1\<^sub>r \<plusminus> -\<^sub>a y \<in> S \<and> 1\<^sub>r \<cdot>\<^sub>r y \<in> S",
       erule conjE)
apply (cut_tac ring_one,
       simp add:aGroup.ag_r_inv1[of "R" "1\<^sub>r"])
done

lemma (in Ring) Sr_mOp_closed:"\<lbrakk>sr R S; x \<in> S\<rbrakk> \<Longrightarrow> -\<^sub>a x \<in> S"
apply (frule Sr_zero[of "S"])
apply (simp add:sr_def, (erule conjE)+)
apply (cut_tac ring_is_ag)
 apply (frule_tac x = "\<zero>" in bspec, assumption,
        thin_tac "\<forall>x\<in>S. \<forall>y\<in>S. x \<plusminus> -\<^sub>a y \<in> S \<and> x \<cdot>\<^sub>r y \<in> S",
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>y\<in>S. \<zero> \<plusminus> -\<^sub>a y \<in> S \<and> \<zero> \<cdot>\<^sub>r y \<in> S", erule conjE)
 apply (frule subsetD[of "S" "carrier R" "\<zero>"], assumption+,
        frule subsetD[of "S" "carrier R" "x"], assumption+)
 apply (frule aGroup.ag_mOp_closed [of "R" "x"], assumption)
 apply (simp add:aGroup.ag_l_zero)
done

lemma (in Ring) Sr_pOp_closed:"\<lbrakk>sr R S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<plusminus> y \<in> S"
apply (frule Sr_mOp_closed[of "S" "y"], assumption+)
apply (unfold sr_def, (erule conjE)+)
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>S. \<forall>y\<in>S. x \<plusminus> -\<^sub>a y \<in> S \<and> x \<cdot>\<^sub>r y \<in> S",
        frule_tac x = "-\<^sub>a y" in bspec, assumption,
        thin_tac "\<forall>y\<in>S. x \<plusminus> -\<^sub>a y \<in> S \<and> x \<cdot>\<^sub>r y \<in> S", erule conjE)

 apply (cut_tac ring_is_ag )
 apply (frule subsetD[of "S" "carrier R" "y"], assumption+)
 apply (simp add:aGroup.ag_inv_inv)
done

lemma (in Ring) Sr_tOp_closed:"\<lbrakk>sr R S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>r y \<in> S"
by (simp add:sr_def)

lemma (in Ring) Sr_ring:"sr R S \<Longrightarrow> Ring (Sr R S)"
apply (simp add:Ring_def [of "Sr R S"],
       cut_tac ring_is_ag)
 apply (rule conjI)
 apply (simp add:Sr_def Sr_pOp_closed)

apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:Sr_def,
        frule_tac x = a and y = b in Sr_pOp_closed, assumption+,
        frule_tac x = b and y = c in Sr_pOp_closed, assumption+,
        simp add:Sr_def sr_def, (erule conjE)+)
 apply (frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
        frule_tac c = b in subsetD[of "S" "carrier R"], assumption+,
        frule_tac c = c in subsetD[of "S" "carrier R"], assumption+)
 apply (simp add:aGroup.ag_pOp_assoc)

apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:Sr_def sr_def, (erule conjE)+,
        frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
        frule_tac c = b in subsetD[of "S" "carrier R"], assumption+)
 apply (simp add:aGroup.ag_pOp_commute)

apply (rule conjI)
  apply ((subst Sr_def)+, simp)
  apply (simp add:Sr_mOp_closed)

apply (rule conjI)
  apply (rule allI)
  apply ((subst Sr_def)+, simp add:Sr_mOp_closed, rule impI)
  apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
         simp add:aGroup.ag_l_inv1)

apply (rule conjI)
  apply (simp add:Sr_def Sr_zero)

apply (rule conjI)
  apply (rule allI, simp add:Sr_def Sr_zero)
  apply (rule impI)
  apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
         simp add:aGroup.ag_l_zero)

apply (rule conjI)
  apply (simp add:Sr_def Sr_tOp_closed)

apply (rule conjI)
  apply (rule allI, rule impI)+
  apply (simp add:Sr_def Sr_tOp_closed)
  apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
         frule_tac c = b in subsetD[of "S" "carrier R"], assumption+,
         frule_tac c = c in subsetD[of "S" "carrier R"], assumption+)
  apply (simp add:ring_tOp_assoc)

apply (rule conjI)
  apply ((rule allI, rule impI)+, simp add:Sr_def)
  apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
         frule_tac c = b in subsetD[of "S" "carrier R"], assumption+,
         simp add:ring_tOp_commute)

apply (rule conjI)
  apply (simp add:Sr_def Sr_one)

apply (rule conjI)
  apply (simp add:Sr_def Sr_pOp_closed Sr_tOp_closed)
  apply (rule allI, rule impI)+
  apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+,
         frule_tac c = b in subsetD[of "S" "carrier R"], assumption+,
         frule_tac c = c in subsetD[of "S" "carrier R"], assumption+)
  apply (simp add:ring_distrib1)

apply (simp add:Sr_def Sr_one)
 apply (rule allI, rule impI)
   apply (unfold sr_def, frule conjunct1, fold sr_def,
         frule_tac c = a in subsetD[of "S" "carrier R"], assumption+)
 apply (simp add:ring_l_one)
done


section "Calculation of elements"
 (** The author of this part is L. Chen, revised by H. Murao and Y.
     Santo  **)

subsection "nscale"

lemma (in Ring) ring_tOp_rel:"\<lbrakk>x\<in>carrier R; xa\<in>carrier R; y\<in>carrier R;
ya \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<cdot>\<^sub>r xa) \<cdot>\<^sub>r (y \<cdot>\<^sub>r ya) = (x \<cdot>\<^sub>r y) \<cdot>\<^sub>r (xa \<cdot>\<^sub>r ya)"
apply (frule ring_tOp_closed[of "y" "ya"], assumption+,
       simp add:ring_tOp_assoc[of "x" "xa"])
apply (simp add:ring_tOp_assoc[THEN sym, of "xa" "y" "ya"],
       simp add:ring_tOp_commute[of "xa" "y"],
       simp add:ring_tOp_assoc[of "y" "xa" "ya"])
apply (frule ring_tOp_closed[of "xa" "ya"], assumption+,
       simp add:ring_tOp_assoc[THEN sym, of "x" "y"])
done

lemma (in Ring) nsClose:
  "\<And> n. \<lbrakk> x \<in> carrier R \<rbrakk>  \<Longrightarrow> nscal R x n \<in> carrier R"
  apply (induct_tac n)
  apply (simp add:ring_zero)
  apply (cut_tac ring_is_ag, simp add:aGroup.ag_pOp_closed)
done

lemma (in Ring) nsZero:
             "nscal R \<zero> n = \<zero>"
  apply (cut_tac ring_is_ag)
  apply (induct_tac n)
  apply simp

  apply simp
   apply (cut_tac ring_zero, simp add:aGroup.ag_l_zero)
  done

lemma (in Ring) nsZeroI: "\<And> n.  x = \<zero>  \<Longrightarrow> nscal R x n = \<zero>"
  by (simp only:nsZero)

lemma (in Ring) nsEqElm:  "\<lbrakk> x \<in> carrier R; y \<in> carrier R; x = y \<rbrakk>
        \<Longrightarrow> (nscal R x n) = (nscal R y n)"
  by simp

lemma (in Ring) nsDistr:  "x \<in> carrier R
        \<Longrightarrow> (nscal R x n) \<plusminus> (nscal R x m) = nscal R x (n + m)"
apply (cut_tac ring_is_ag)
  apply (induct_tac m)
  apply simp
  apply (frule nsClose[of "x" "n"])
  apply ( simp add:aGroup.ag_r_zero)

  apply simp
  apply (frule_tac x = x and n = n in nsClose,
         frule_tac x = x and n = na in nsClose)
  apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+, simp)
  done

lemma (in Ring) nsDistrL:  "\<lbrakk>x \<in> carrier R; y \<in> carrier R \<rbrakk>
        \<Longrightarrow> (nscal R x n) \<plusminus> (nscal R y n) = nscal R (x \<plusminus> y) n"
  apply (cut_tac ring_is_ag)
  apply (induct_tac n)
  apply simp
  apply (cut_tac ring_zero,
         simp add:aGroup.ag_l_zero)

  apply simp
  apply (frule_tac x = x and n = n in nsClose,
         frule_tac x = y and n = n in nsClose)
  apply (subst aGroup.pOp_assocTr43[of R _ x _ y], assumption+)
  apply (frule_tac x = x and y = "n \<times>\<^bsub>R\<^esub> y" in aGroup.ag_pOp_commute[of "R"],
         assumption+)
   apply simp
   apply (subst aGroup.pOp_assocTr43[THEN sym, of R _ _ x y], assumption+)
   apply simp
done

lemma (in Ring) nsMulDistrL:"\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r (nscal R y n) = nscal R (x \<cdot>\<^sub>r y) n"
  apply (induct_tac n)
  apply simp
  apply (simp add:ring_times_x_0)

  apply simp apply (subst ring_distrib1, assumption+)
  apply (rule nsClose, assumption+)
  apply simp
done

lemma (in Ring) nsMulDistrR:"\<lbrakk> x \<in> carrier R; y \<in> carrier R\<rbrakk>
        \<Longrightarrow> (nscal R y n) \<cdot>\<^sub>r x = nscal R (y \<cdot>\<^sub>r x) n"
  apply (frule_tac x = y and n = n in nsClose,
         simp add:ring_tOp_commute[of "n \<times>\<^bsub>R\<^esub> y" "x"],
         simp add:nsMulDistrL,
         simp add:ring_tOp_commute[of "y" "x"])
done

subsection "npow"

lemma (in Ring) npClose:"x \<in> carrier R \<Longrightarrow> npow R x n \<in> carrier R"
  apply (induct_tac n)
  apply simp apply (simp add:ring_one)

  apply simp
  apply (rule ring_tOp_closed, assumption+)
  done

lemma (in Ring) npMulDistr:"\<And> n m. x \<in> carrier R  \<Longrightarrow>
                 (npow R x n) \<cdot>\<^sub>r (npow R x m) = npow R x (n + m)"
  apply (induct_tac m)
  apply simp apply (rule ring_r_one, simp add:npClose)

  apply simp
  apply (frule_tac x = x and n = n in npClose,
         frule_tac x = x and n = na in npClose)
  apply (simp add:ring_tOp_assoc[THEN sym])
done

lemma (in Ring) npMulExp:"\<And>n m. x \<in> carrier R
        \<Longrightarrow>  npow R (npow R x n) m = npow R x (n * m)"
apply (induct_tac m)
apply simp
apply simp
apply (simp add:npMulDistr)
apply (simp add:add.commute)
done


lemma (in Ring) npGTPowZero_sub:
  " \<And> n. \<lbrakk> x \<in> carrier R; npow R x m = \<zero> \<rbrakk>
        \<Longrightarrow>(m \<le> n) \<longrightarrow> (npow R x n = \<zero> )"
  apply (rule impI)
  apply (subgoal_tac "npow R x n = (npow R x (n-m)) \<cdot>\<^sub>r (npow R x m)")
  apply simp
  apply (rule ring_times_x_0) apply (simp add:npClose)
  apply (thin_tac "x^\<^bsup>R m\<^esup> = \<zero>")
  apply (subst npMulDistr, assumption)
  apply simp
  done

lemma (in Ring) npGTPowZero:
  "\<And> n. \<lbrakk> x \<in> carrier R; npow R x m = \<zero>; m \<le> n \<rbrakk>
        \<Longrightarrow> npow R x n = \<zero>"
  apply (cut_tac x = x and m = m and n = n in npGTPowZero_sub, assumption+)
  apply simp
  done


lemma (in Ring) npOne: " npow R (1\<^sub>r) n = 1\<^sub>r"
  apply (induct_tac n) apply simp

  apply simp
    apply (rule ring_r_one, simp add:ring_one)
done

lemma (in Ring) npZero_sub: "0 < n \<longrightarrow> npow R \<zero> n = \<zero>"
  apply (induct_tac "n")
  apply simp

  apply simp
    apply (cut_tac ring_zero,
           frule_tac n = n in npClose[of "\<zero>"])
    apply (simp add:ring_times_x_0)
done

lemma (in Ring) npZero: "0 < n  \<Longrightarrow> npow R \<zero> n = \<zero>"
  apply (simp add:npZero_sub)
done

lemma (in Ring) npMulElmL: "\<And> n. \<lbrakk> x \<in> carrier R; 0 \<le> n\<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r (npow R x n) = npow R x (Suc n)"
apply (simp only:npow_suc,
       frule_tac n = n and x = x in npClose,
       simp add:ring_tOp_commute)
done

lemma (in Ring) npMulEleL: "\<And> n. x \<in> carrier R
        \<Longrightarrow> (npow R x n) \<cdot>\<^sub>r x =  npow R x (Suc n)"
by (simp add:npMulElmL[THEN sym])

lemma (in Ring) npMulElmR: "\<And> n. x \<in> carrier R
        \<Longrightarrow> (npow R x n) \<cdot>\<^sub>r x =  npow R x (Suc n)"
  apply ( frule_tac n = n in npClose[of "x"])
   apply (simp only:ring_tOp_commute,
          subst npMulElmL, assumption, simp, simp)
  done

lemma (in Ring) np_1:"a \<in> carrier R \<Longrightarrow> npow R a (Suc 0) = a"  (* Y. Santo*)
apply simp
 apply (simp add:ring_l_one)
done

subsection  "nsum and fSum"

lemma (in aGroup) nsum_memTr: "(\<forall>j \<le> n. f j \<in> carrier A) \<longrightarrow>
                                 nsum A f n \<in> carrier A"
  apply (induct_tac "n")
  apply simp
  apply (rule impI)
  apply (cut_tac n = n in Nsetn_sub_mem1, simp)
  apply (frule_tac a = "Suc n" in forall_spec, simp,
         thin_tac "\<forall>j\<le>Suc n. f j \<in> carrier A")
   apply (rule ag_pOp_closed, assumption+)
   done

lemma (in aGroup) nsum_mem:"\<forall>j \<le> n. f j \<in> carrier A \<Longrightarrow>
                                 nsum A f n \<in> carrier A"
apply (simp add:nsum_memTr)
done

lemma (in aGroup) nsum_eqTr:"(\<forall>j \<le> n. f j \<in> carrier A \<and>
                                      g j \<in> carrier A \<and>
                                      f j = g j)
                           \<longrightarrow>  nsum A f n = nsum A g n"
apply (induct_tac n)
 apply simp
apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
done

lemma (in aGroup) nsum_eq:"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier A; \<forall>j \<le> n. g j \<in> carrier A;
                           \<forall>j \<le> n. f j = g j\<rbrakk> \<Longrightarrow>  nsum A f n = nsum A g n"
by (simp add:nsum_eqTr)

lemma (in aGroup) nsum_cmp_assoc:"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier A;
       g \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n}; h \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n}\<rbrakk> \<Longrightarrow>
       nsum A (cmp (cmp f h) g) n = nsum A (cmp f (cmp h g)) n"
apply (rule nsum_eq)
apply (rule allI, rule impI, simp add:cmp_def)
apply (frule_tac x = j in funcset_mem[of g "{j. j \<le> n}" "{j. j \<le> n}"], simp,
       frule_tac x = "g j" in funcset_mem[of h "{j. j \<le> n}" "{j. j \<le> n}"],
       assumption, simp)
 apply (rule allI, rule impI, simp add:cmp_def,
       frule_tac x = j in funcset_mem[of g "{j. j \<le> n}" "{j. j \<le> n}"], simp,
       frule_tac x = "g j" in funcset_mem[of h "{j. j \<le> n}" "{j. j \<le> n}"],
       assumption, simp)
 apply (rule allI, simp add:cmp_def)
done

lemma (in aGroup) fSum_Suc:"\<forall>j \<in> nset n (n + Suc m). f j \<in> carrier A \<Longrightarrow>
              fSum A f n (n + Suc m) = fSum A f n (n + m) \<plusminus> f (n + Suc m)"
by (simp add:fSum_def, simp add:cmp_def slide_def)

lemma (in aGroup) fSum_eqTr:"(\<forall>j \<in> nset n (n + m). f j \<in> carrier A \<and>
         g j \<in> carrier A \<and>  f j = g j)  \<longrightarrow>
                       fSum A f  n (n + m) = fSum A g n (n + m)"
apply (induct_tac m)
 apply (simp add:fSum_def,
        simp add:cmp_def slide_def,
        simp add:nset_def)

apply (rule impI)
 apply (subst fSum_Suc,
        rule ballI, simp, simp)
 apply (cut_tac n = n and m = na and f = g in fSum_Suc,
        rule ballI, simp, simp,
        thin_tac "\<Sigma>\<^sub>f A g n (Suc (n + na)) =
                                   \<Sigma>\<^sub>f A g n (n + na) \<plusminus> g (Suc (n + na))")

 apply (cut_tac n = n and m = na in nsetnm_sub_mem, simp,
        thin_tac "\<forall>j. j \<in> nset n (n + na) \<longrightarrow> j \<in> nset n (Suc (n + na))")
apply (frule_tac x = "Suc (n + na)" in bspec,
       simp add:nset_def, simp)
done

lemma (in aGroup) fSum_eq:"\<lbrakk> \<forall>j \<in> nset n (n + m). f j \<in> carrier A;
      \<forall>j \<in> nset n (n + m). g j \<in> carrier A; (\<forall>j\<in> nset n (n + m). f j = g j)\<rbrakk>
       \<Longrightarrow>
         fSum A f n (n + m) = fSum A g n (n + m)"
by (simp add:fSum_eqTr)

lemma (in aGroup) fSum_eq1:"\<lbrakk>n \<le> m; \<forall>j\<in>nset n m. f j \<in> carrier A;
       \<forall>j\<in>nset n m. g j \<in> carrier A;  \<forall>j\<in>nset n m. f j = g j\<rbrakk> \<Longrightarrow>
         fSum A f n m = fSum A g n m"
apply (cut_tac fSum_eq[of n "m - n" f g])
apply simp+
done

lemma (in aGroup) fSum_zeroTr:"(\<forall>j \<in> nset n (n + m). f j = \<zero>)  \<longrightarrow>
                       fSum A f  n (n + m) = \<zero>"
apply (induct_tac m)
 apply (simp add:fSum_def cmp_def slide_def nset_def)
 apply (rule impI)
 apply (subst fSum_Suc)
 apply (rule ballI, simp add:ag_inc_zero)
apply (frule_tac x = "n + Suc na" in bspec, simp add:nset_def,
       simp)
 apply (simp add:nset_def)
 apply (cut_tac ag_inc_zero, simp add:ag_l_zero)
done

lemma (in aGroup) fSum_zero:"\<forall>j \<in> nset n (n + m). f j = \<zero>  \<Longrightarrow>
                       fSum A f  n (n + m) = \<zero>"
by (simp add:fSum_zeroTr)

lemma (in aGroup) fSum_zero1:"\<lbrakk>n < m; \<forall>j \<in> nset (Suc n) m. f j = \<zero>\<rbrakk>  \<Longrightarrow>
                       fSum A f  (Suc n) m = \<zero>"
apply (cut_tac fSum_zero[of "Suc n" "m - Suc n" f])
 apply simp+
done

lemma (in Ring) nsumMulEleL: "\<And> n. \<lbrakk> \<forall> i. f i \<in> carrier R; x \<in> carrier R \<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r (nsum R f n) = nsum R (\<lambda> i. x \<cdot>\<^sub>r (f i)) n"
  apply (cut_tac ring_is_ag)
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (subst ring_distrib1, assumption)
  apply (rule aGroup.nsum_mem, assumption)
 apply (rule allI, simp+)
done

lemma (in Ring) nsumMulElmL:
  "\<And> n. \<lbrakk> \<forall> i. f i \<in> carrier R; x \<in> carrier R \<rbrakk>
        \<Longrightarrow> x \<cdot>\<^sub>r (nsum R f n) = nsum R (\<lambda> i. x \<cdot>\<^sub>r (f i)) n"
  apply (cut_tac ring_is_ag)
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (subst ring_distrib1, assumption+)
    apply (simp add:aGroup.nsum_mem)+
  done

lemma (in aGroup) nsumTailTr:
         "(\<forall>j\<le>(Suc n). f j \<in> carrier A) \<longrightarrow>
          nsum A f (Suc n) = (nsum A (\<lambda> i. (f (Suc i))) n) \<plusminus> (f 0)"
  apply (induct_tac "n")
  apply simp
  apply (rule impI,
         rule ag_pOp_commute)
  apply (cut_tac Nset_inc_0[of "Suc 0"],
         simp add:Pi_def,
         cut_tac n_in_Nsetn[of "Suc 0"],
         simp add:Pi_def)

  apply (rule impI)
   apply (cut_tac n = "Suc n" in Nsetn_sub_mem1, simp)
   apply (frule_tac a = 0 in forall_spec, simp,
          frule_tac a = "Suc (Suc n)" in forall_spec, simp)
    apply (cut_tac n = n in nsum_mem[of  _  "\<lambda>i. f (Suc i)"],
          rule allI, rule impI,
          frule_tac a = "Suc j" in forall_spec, simp, simp,
          thin_tac "\<forall>j\<le>Suc (Suc n). f j \<in> carrier A")
    apply (subst ag_pOp_assoc, assumption+)
       apply (simp add:ag_pOp_commute[of  "f 0"])
    apply (subst ag_pOp_assoc[THEN sym], assumption+)
    apply simp
  done

lemma (in aGroup) nsumTail:
      "\<forall>j \<le> (Suc n). f j \<in> carrier A \<Longrightarrow>
            nsum A f (Suc n) = (nsum A (\<lambda> i. (f (Suc i))) n) \<plusminus> (f 0)"
  by (cut_tac nsumTailTr[of n f], simp)

lemma (in aGroup) nsumElmTail:
  "\<forall>i. f i \<in> carrier A
        \<Longrightarrow> nsum A f (Suc n) = (nsum A (\<lambda> i. (f (Suc i))) n) \<plusminus> (f 0)"
  apply (cut_tac n = n and f = f in nsumTail,
         rule allI, simp, simp)
done

lemma (in aGroup) nsum_addTr:
  "(\<forall>j \<le> n. f j \<in> carrier A \<and> g j \<in> carrier A) \<longrightarrow>
   nsum A (\<lambda> i. (f i) \<plusminus> (g i)) n = (nsum A f n) \<plusminus> (nsum A g n)"
  apply (induct_tac "n")
  apply simp

  apply (simp, rule impI)
  apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (thin_tac "\<Sigma>\<^sub>e A (\<lambda>i. f i \<plusminus> g i) n = \<Sigma>\<^sub>e A f n \<plusminus> \<Sigma>\<^sub>e A g n")
  apply (rule aGroup.ag_add4_rel, rule aGroup_axioms)
  apply (rule aGroup.nsum_mem, rule aGroup_axioms, rule allI, simp)
  apply (rule aGroup.nsum_mem, rule aGroup_axioms, rule allI, simp)
  apply simp+
  done

lemma (in aGroup) nsum_add:
  "\<lbrakk> \<forall>j \<le> n. f j \<in> carrier A; \<forall>j \<le> n. g j \<in> carrier A\<rbrakk>  \<Longrightarrow>
   nsum A (\<lambda> i. (f i) \<plusminus> (g i)) n = (nsum A f n) \<plusminus> (nsum A g n)"
by (cut_tac nsum_addTr[of n f g], simp)

lemma (in aGroup) nsumElmAdd:
  "\<lbrakk> \<forall> i. f i \<in> carrier A; \<forall> i. g i \<in> carrier A\<rbrakk>
        \<Longrightarrow> nsum A (\<lambda> i. (f i) \<plusminus> (g i)) n = (nsum A f n) \<plusminus> (nsum A g n)"
 apply (cut_tac nsum_add[of n f g])
 apply simp
 apply (rule allI, simp)+
 done

lemma (in aGroup) nsum_add_nmTr:
  "(\<forall>j \<le> n. f j \<in> carrier A) \<and> (\<forall>j \<le> m. g j \<in> carrier A) \<longrightarrow>
   nsum A (jointfun n f m g) (Suc (n + m)) = (nsum A f n) \<plusminus> (nsum A g m)"
apply (induct_tac m)
 apply (simp add:jointfun_def sliden_def)
 apply (rule impI)
 apply (rule ag_pOp_add_r)
 apply (rule nsum_mem, rule allI, erule conjE, rule impI, simp)
 apply (erule conjE, simp add:nsum_mem, simp)
 apply (rule nsum_eq[of n], simp+)
apply (simp add:jointfun_def)
 apply (rule impI, simp)
 apply (erule conjE, simp add:sliden_def)
 apply (thin_tac "\<Sigma>\<^sub>e A (\<lambda>i. if i \<le> n then f i else g (sliden (Suc n) i))
        (n + na) \<plusminus> g na = \<Sigma>\<^sub>e A f n \<plusminus> \<Sigma>\<^sub>e A g na")
 apply (subst ag_pOp_assoc)
 apply (simp add:nsum_mem)
 apply (simp add:nsum_mem, simp)
 apply simp
done

lemma (in aGroup) nsum_add_nm:
"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier A; \<forall>j \<le> m. g j \<in> carrier A\<rbrakk> \<Longrightarrow>
   nsum A (jointfun n f m g) (Suc (n + m)) = (nsum A f n) \<plusminus> (nsum A g m)"
apply (cut_tac nsum_add_nmTr[of n f m g])
 apply simp
done

lemma (in Ring) npeSum2_sub_muly:
  "\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
        y \<cdot>\<^sub>r(nsum R (\<lambda>i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>r (npow R y i))
                                (n choose i)) n)
        = nsum R (\<lambda>i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>r (npow R y (i+1)))
                                (n choose i)) n"
  apply (cut_tac ring_is_ag)
  apply (subst nsumMulElmL)
    apply (rule allI)
      apply (simp only:nsClose add:ring_tOp_closed
             add:npClose)
    apply assumption
  apply (simp only:nsMulDistrL add:nsClose add:ring_tOp_closed
         add:npClose)
  apply (simp only: rMulLC [of "y"] add:npClose)

 apply (simp del:npow_suc add:ring_tOp_commute[of y])
 apply (rule aGroup.nsum_eq, assumption)
  apply (rule allI, rule impI, rule nsClose,
         rule ring_tOp_closed, simp add:npClose,
         rule ring_tOp_closed, assumption, simp add:npClose)
  apply (rule allI, rule impI, rule nsClose,
         rule ring_tOp_closed, simp add:npClose,
         rule npClose, assumption)
 apply (rule allI, rule impI)
  apply (frule_tac n = j in npClose[of y])
  apply (simp add:ring_tOp_commute[of y])
done

(********)(********)(********)(********)
lemma binomial_n0: "(Suc n choose 0) = (n choose 0)"
  by simp

lemma binomial_ngt_diff:
  "(n choose Suc n) = (Suc n choose Suc n) - (n choose n)"
  by (subst binomial_Suc_Suc, arith)


lemma binomial_ngt_0: "(n choose Suc n) = 0"
  apply (subst binomial_ngt_diff,
         (subst binomial_n_n)+)
  apply simp
  done

lemma diffLessSuc: "m \<le> n \<Longrightarrow> Suc (n-m) = Suc n - m"
  by arith

lemma (in Ring) npow_suc_i:
  "\<lbrakk> x \<in> carrier R; i \<le> n \<rbrakk>
        \<Longrightarrow> npow R x (Suc n - i) =  x \<cdot>\<^sub>r (npow R x (n-i))"
  apply (subst diffLessSuc [THEN sym, of "i" "n"], assumption)
  apply (frule_tac n = "n - i" in npClose,
         simp add:ring_tOp_commute[of x])
  done
(**
lemma (in Ring) nsumEqFunc_sub:
  "\<lbrakk>  \<And> i. f i \<in> carrier R; \<And> i. g i \<in> carrier R \<rbrakk>
        \<Longrightarrow> ( \<forall> i. i \<le> n \<longrightarrow> f i = g i) \<longrightarrow> (nsum0 R f n = nsum0 R g n)";
  apply (induct_tac "n")
  apply simp+
  done

lemma (in Ring) nsumEqFunc:
  "\<lbrakk> \<And> i. f i \<in> carrier R; \<And> i. g i \<in> carrier R;
     \<And> i. i \<le> n \<longrightarrow> f i = g i \<rbrakk> \<Longrightarrow>  nsum0 R f n = nsum0 R g n"
  apply (cut_tac nsumEqFunc_sub [of "f" "g" "n"])
  apply simp+
  done          nsumEqFunc \<longrightarrow> nsum_eq       **)
(********)(********)

lemma (in Ring) npeSum2_sub_mulx: "\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
  x \<cdot>\<^sub>r (nsum R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>r (npow R y i))
                                                        (n choose i)) n)
   = (nsum R (\<lambda>i. nscal R
                          ((npow R x (Suc n - Suc i)) \<cdot>\<^sub>r (npow R y (Suc i)))
                          (n choose Suc i)) n) \<plusminus>
                (nscal R ((npow R x (Suc n - 0)) \<cdot>\<^sub>r (npow R y 0))
                        (Suc n choose 0))"
  apply (cut_tac ring_is_ag)
  apply (simp only: binomial_n0)
  apply (subst aGroup.nsumElmTail [THEN sym, of R "\<lambda> i. nscal R ((npow R x (Suc n - i)) \<cdot>\<^sub>r (npow R y i)) (n choose i)"], assumption+)
  apply (rule allI)
      apply (simp only:nsClose add:ring_tOp_closed add:npClose)

  apply (simp only:nsum_suc)
  apply (subst binomial_ngt_0)
  apply (simp only:nscal_0)
  apply (subst aGroup.ag_r_zero, assumption)
    apply (simp add:aGroup.nsum_mem nsClose ring_tOp_closed npClose)
  apply (subst nsumMulElmL [of  _ "x"])
    apply (rule allI, rule nsClose, rule ring_tOp_closed, simp add:npClose,
           simp add:npClose, assumption)

  apply (simp add: nsMulDistrL [of "x"] ring_tOp_closed npClose)
  apply (simp add:ring_tOp_assoc [THEN sym, of "x"] npClose)
  apply (rule aGroup.nsum_eq, assumption)
   apply (rule allI, rule impI,
          rule nsClose, (rule ring_tOp_closed)+, assumption,
          simp add:npClose, simp add:npClose)
   apply (rule allI, rule impI,
          rule nsClose, rule ring_tOp_closed,
          simp add:npClose, simp add:npClose)
  apply (rule allI, rule impI)
  apply (frule_tac n = "n - j" in npClose[of x],
        simp add:ring_tOp_commute[of x],
        subst npow_suc[THEN sym])
  apply (simp add:Suc_diff_le)
done

lemma (in Ring) npeSum2_sub_mulx2:
  "\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
        x \<cdot>\<^sub>r (nsum R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>r (npow R y i))
                                (n choose i)) n)
        = (nsum R  (\<lambda>i. nscal R
                          ((npow R x (n - i)) \<cdot>\<^sub>r ((npow R y i) \<cdot>\<^sub>r y ))
                          (n choose Suc i)) n) \<plusminus>
                (\<zero> \<plusminus> ((x \<cdot>\<^sub>r (npow R x n)) \<cdot>\<^sub>r (1\<^sub>r)))"
apply (subst  npeSum2_sub_mulx, assumption+, simp)
apply (frule npClose[of x n])
apply (subst ring_tOp_commute[of x], assumption+)
 apply (cut_tac ring_is_ag)
 apply (cut_tac aGroup.nsum_eq[of R n
        "\<lambda>i.  (n choose Suc i) \<times>\<^bsub>R\<^esub> (x^\<^bsup>R (n - i)\<^esup> \<cdot>\<^sub>r y^\<^bsup>R (Suc i)\<^esup>)"
        "\<lambda>i.  (n choose Suc i) \<times>\<^bsub>R\<^esub> (x^\<^bsup>R (n - i)\<^esup> \<cdot>\<^sub>r (y^\<^bsup>R i\<^esup> \<cdot>\<^sub>r y))"])
 apply (simp del:npow_suc)+
  apply (rule allI, rule impI,
         rule nsClose, rule ring_tOp_closed, simp add:npClose,
         simp only:npClose)
  apply (rule allI, rule impI,
         rule nsClose, rule ring_tOp_closed, simp add:npClose,
         rule ring_tOp_closed, simp add:npClose, assumption)
  apply (rule allI, rule impI)
 apply (frule_tac n = j in npClose[of y])
 apply simp
done


lemma (in Ring) npeSum2:
  "\<And> n. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk>
        \<Longrightarrow> npow R (x \<plusminus> y) n =
                nsum R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>r (npow R y i))
                                       ( n choose i) ) n"
  apply (cut_tac ring_is_ag)
  apply (induct_tac "n")

  (*1*)
  apply simp
    apply (cut_tac ring_one, simp add:ring_r_one, simp add:aGroup.ag_l_zero)
  (*1:done*)

  apply (subst aGroup.nsumElmTail, assumption+)
    apply (rule allI)
    apply (simp add:nsClose ring_tOp_closed npClose)

(**
thm binomial_Suc_Suc
**)
  apply (simp only:binomial_Suc_Suc)
  apply (simp only: nsDistr [THEN sym] add:npClose ring_tOp_closed)
  apply (subst aGroup.nsumElmAdd, assumption+)
    apply (rule allI,
           simp add:nsClose ring_tOp_closed npClose)
    apply (rule allI,
           simp add:nsClose add:ring_tOp_closed npClose)
  apply (subst aGroup.ag_pOp_assoc, assumption)
    apply (rule aGroup.nsum_mem, assumption,
           rule allI, rule impI,  simp add:nsClose ring_tOp_closed npClose)
    apply (rule aGroup.nsum_mem, assumption,
           rule allI, rule impI,  simp add:nsClose ring_tOp_closed npClose)
    apply (simp add:nsClose ring_tOp_closed npClose)
    apply (rule aGroup.ag_pOp_closed, assumption)
    apply (simp add:aGroup.ag_inc_zero)
    apply (rule ring_tOp_closed)+
    apply (simp add:npClose, assumption, simp add:ring_one)

  apply (subst npMulElmL [THEN sym, of "x \<plusminus> y"],
         simp add:aGroup.ag_pOp_closed, simp)
   apply simp
  apply (subst ring_distrib2 [of _ "x" "y"])
  apply (rule aGroup.nsum_mem,assumption,
         rule allI, rule impI, rule nsClose, rule ring_tOp_closed,
         simp add:npClose, simp add:npClose, assumption+)
  apply (rule aGroup.gEQAddcross [THEN sym], assumption+,
         rule aGroup.nsum_mem, assumption, rule allI, rule impI, rule nsClose,
         (rule ring_tOp_closed)+, simp add:npClose,
         rule ring_tOp_closed, simp add:npClose, assumption)
    apply (rule aGroup.ag_pOp_closed, assumption)
    apply (rule aGroup.nsum_mem, assumption,
           rule allI, rule impI, rule nsClose, rule ring_tOp_closed,
          simp add:npClose, rule ring_tOp_closed, simp add:npClose, assumption)
    apply (rule aGroup.ag_pOp_closed, assumption, simp add:ring_zero)
    apply ((rule ring_tOp_closed)+,
           simp add:npClose,assumption, simp add:ring_one)
    apply (rule ring_tOp_closed, assumption,
           rule aGroup.nsum_mem, assumption, rule allI, rule impI,
           rule nsClose, rule ring_tOp_closed,
           (simp add:npClose)+)
    apply (rule ring_tOp_closed, assumption+,
           rule aGroup.nsum_mem, assumption, rule allI, rule impI,
           rule nsClose,
           rule ring_tOp_closed,
           simp add:npClose, simp add:npClose)
    apply (subst npeSum2_sub_muly [of "x" "y"], assumption+, simp)

  (* final part *)
  apply (subst npeSum2_sub_mulx2 [of x y], assumption+)
  apply (frule_tac n = na in npClose[of x],
         simp add:ring_tOp_commute[of _ x])
  done

lemma (in aGroup) nsum_zeroTr:
  "\<And> n. (\<forall> i. i \<le> n \<longrightarrow>  f i = \<zero>) \<longrightarrow> (nsum A f n = \<zero>)"
  apply (induct_tac "n")
  apply simp

  apply (rule impI)
  apply (cut_tac n = na in Nsetn_sub_mem1, simp)
    apply (subst aGroup.ag_l_zero, rule aGroup_axioms)
    apply (simp add:ag_inc_zero)
  apply simp
  done

lemma (in Ring) npAdd:
  "\<lbrakk> x \<in> carrier R; y \<in> carrier R;
     npow R x m = \<zero>; npow R y n = \<zero> \<rbrakk>
        \<Longrightarrow> npow R (x \<plusminus> y) (m + n) = \<zero>"
  apply (subst npeSum2, assumption+)

  apply (rule aGroup.nsum_zeroTr [THEN mp])
  apply (simp add:ring_is_ag)
  apply (rule allI, rule impI)
  apply (rule nsZeroI)
  apply (rule rMulZeroDiv, simp add:npClose, simp add:npClose)

  apply (case_tac "i \<le> n")

  apply (rule disjI1)
  apply (rule npGTPowZero [of "x" "m"], assumption+)
    apply arith

  apply (rule disjI2)
  apply (rule npGTPowZero [of "y" "n"], assumption+)
    apply (arith)
  done

lemma (in Ring) npInverse:
  "\<And>n. x \<in> carrier R
        \<Longrightarrow> npow R (-\<^sub>a x) n = npow R x n
            \<or> npow R (-\<^sub>a x) n = -\<^sub>a (npow R x n)"
  apply (induct_tac n)
 (* n=0 *)
  apply simp

 apply (erule disjE)
 apply simp
 apply (subst ring_inv1_2,
        simp add:npClose, assumption, simp)
 apply (cut_tac ring_is_ag)

 apply simp
 apply (subst ring_inv1_2[THEN sym, of _ x])
 apply (rule aGroup.ag_mOp_closed, assumption+,
        simp add:npClose, assumption)
 apply (thin_tac "(-\<^sub>a x)^\<^bsup>R na\<^esup> = -\<^sub>a (x^\<^bsup>R na\<^esup>)",
        frule_tac n = na in npClose[of x],
        frule_tac x = "x^\<^bsup>R na\<^esup>" in aGroup.ag_mOp_closed[of R], simp add:npClose)
 apply (simp add: ring_inv1_1[of _ x])
 apply (simp add:aGroup.ag_inv_inv[of R])
done

lemma (in Ring) npMul:
  "\<And> n. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk>
        \<Longrightarrow> npow R (x \<cdot>\<^sub>r y) n = (npow R x n) \<cdot>\<^sub>r (npow R y n)"
  apply (induct_tac "n")
 (* n=0 *)
  apply simp
  apply (rule ring_r_one [THEN sym]) apply (simp add:ring_one)
 (* n>0 *)
  apply (simp only:npow_suc)
  apply (rule ring_tOp_rel[THEN sym])
    apply (rule npClose, assumption+)+
  done

section "Ring homomorphisms"

definition
  rHom :: "[('a, 'm) Ring_scheme, ('b, 'm1) Ring_scheme]
                      \<Rightarrow> ('a  \<Rightarrow> 'b) set" where
  "rHom A R = {f. f \<in> aHom A R \<and>
    (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f ( x \<cdot>\<^sub>r\<^bsub>A\<^esub> y) =  (f x) \<cdot>\<^sub>r\<^bsub>R\<^esub> (f y))
    \<and> f (1\<^sub>r\<^bsub>A\<^esub>) = (1\<^sub>r\<^bsub>R\<^esub>)}"

definition
  rInvim :: "[('a, 'm) Ring_scheme, ('b, 'm1) Ring_scheme, 'a \<Rightarrow> 'b, 'b set]
               \<Rightarrow> 'a set" where
  "rInvim A R f K = {a. a \<in> carrier A \<and> f a \<in> K}"

definition
  rimg :: "[('a, 'm) Ring_scheme, ('b, 'm1) Ring_scheme, 'a \<Rightarrow> 'b] \<Rightarrow>
            'b Ring" where
  "rimg A R f = \<lparr>carrier= f `(carrier A), pop = pop R, mop = mop R,
    zero = zero R, tp = tp R, un = un R \<rparr>"

definition
  ridmap :: "('a, 'm) Ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "ridmap R = (\<lambda>x\<in>carrier R. x)"

definition
  r_isom :: "[('a, 'm) Ring_scheme, ('b, 'm1) Ring_scheme] \<Rightarrow> bool"
                       (infixr "\<cong>\<^sub>r" 100) where
  "r_isom R R' \<longleftrightarrow> (\<exists>f\<in>rHom R R'. bijec\<^bsub>R,R'\<^esub> f)"

definition
  Subring :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme] \<Rightarrow> bool" where
  "Subring R S == Ring S \<and> (carrier S \<subseteq> carrier R) \<and> (ridmap S) \<in> rHom S R"

lemma ridmap_surjec:"Ring A \<Longrightarrow> surjec\<^bsub>A,A\<^esub> (ridmap A)"
by(simp add:surjec_def aHom_def ridmap_def Ring.ring_is_ag aGroup.ag_pOp_closed surj_to_def)

lemma rHom_aHom:"f \<in> rHom A R \<Longrightarrow> f \<in> aHom A R"
by (simp add:rHom_def)

lemma rimg_carrier:"f \<in> rHom A R \<Longrightarrow> carrier (rimg A R f) = f ` (carrier A)"
by (simp add:rimg_def)

lemma rHom_mem:"\<lbrakk> f \<in> rHom A R; a \<in> carrier A \<rbrakk> \<Longrightarrow> f a \<in> carrier R"
apply (simp add:rHom_def, frule conjunct1)
 apply (thin_tac "f \<in> aHom A R \<and>
     (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f (x \<cdot>\<^sub>r\<^bsub>A\<^esub> y) = f x \<cdot>\<^sub>r\<^bsub>R\<^esub> f y) \<and> f 1\<^sub>r\<^bsub>A\<^esub> = 1\<^sub>r\<^bsub>R\<^esub>")
 apply (simp add:aHom_def, frule conjunct1)
 apply (thin_tac "f \<in> carrier A \<rightarrow> carrier R \<and>
     f \<in> extensional (carrier A) \<and>
     (\<forall>a\<in>carrier A. \<forall>b\<in>carrier A. f (a \<plusminus>\<^bsub>A\<^esub> b) = f a \<plusminus>\<^bsub>R\<^esub> f b)")
 apply (simp add:funcset_mem)
done

lemma rHom_func:"f \<in> rHom A R \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier R"
by (simp add:rHom_def aHom_def)

lemma ringhom1:"\<lbrakk> Ring A; Ring R; x \<in> carrier A; y \<in> carrier A;
                    f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (x \<plusminus>\<^bsub>A\<^esub> y) = (f x) \<plusminus>\<^bsub>R\<^esub> (f y)"
apply (simp add:rHom_def) apply (erule conjE)
apply (frule Ring.ring_is_ag [of "A"])
apply (frule Ring.ring_is_ag [of "R"])
apply (rule aHom_add, assumption+)
done

lemma rHom_inv_inv:"\<lbrakk> Ring A; Ring R; x \<in> carrier A; f \<in> rHom A R \<rbrakk>
 \<Longrightarrow> f (-\<^sub>a\<^bsub>A\<^esub> x) = -\<^sub>a\<^bsub>R\<^esub> (f x)"
apply (frule Ring.ring_is_ag [of "A"],
       frule Ring.ring_is_ag [of "R"])
apply (simp add:rHom_def, erule conjE)
apply (simp add:aHom_inv_inv)
done

lemma rHom_0_0:"\<lbrakk> Ring A; Ring R; f \<in> rHom A R \<rbrakk>  \<Longrightarrow> f (\<zero>\<^bsub>A\<^esub>) = \<zero>\<^bsub>R\<^esub>"
apply (frule Ring.ring_is_ag [of "A"], frule Ring.ring_is_ag [of "R"])
apply (simp add:rHom_def, (erule conjE)+, simp add:aHom_0_0)
done

lemma rHom_tOp:"\<lbrakk> Ring A; Ring R; x \<in> carrier A; y \<in> carrier A;
 f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (x \<cdot>\<^sub>r\<^bsub>A\<^esub> y) = (f x) \<cdot>\<^sub>r\<^bsub>R\<^esub> (f y)"
by (simp add:rHom_def)

lemma rHom_add:"\<lbrakk>f \<in> rHom A R; x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow>
                   f (x \<plusminus>\<^bsub>A\<^esub> y) = (f x) \<plusminus>\<^bsub>R\<^esub> (f y)"
by (simp add:rHom_def aHom_def)

lemma rHom_one:"\<lbrakk> Ring A; Ring R;f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (1\<^sub>r\<^bsub>A\<^esub>) = (1\<^sub>r\<^bsub>R\<^esub>)"
by (simp add:rHom_def)

lemma rHom_npow:"\<lbrakk> Ring A; Ring R; x \<in> carrier A; f \<in> rHom A R \<rbrakk> \<Longrightarrow>
                    f (x^\<^bsup>A n\<^esup>) = (f x)^\<^bsup>R n\<^esup>"
apply (induct_tac n)
apply (simp add:rHom_one)
apply (simp,
      frule_tac n = n in Ring.npClose[of "A" "x"], assumption+,
      subst rHom_tOp[of "A" "R" _ "x" "f"], assumption+, simp)
done

lemma rHom_compos:"\<lbrakk>Ring A; Ring B; Ring C; f \<in> rHom A B; g \<in> rHom B C\<rbrakk> \<Longrightarrow>
                   compos A g f \<in> rHom A C"
apply (subst rHom_def, simp)
apply (frule Ring.ring_is_ag[of "A"], frule Ring.ring_is_ag[of "B"],
       frule Ring.ring_is_ag[of "C"],
       frule rHom_aHom[of "f" "A" "B"], frule rHom_aHom[of "g" "B" "C"],
       simp add:aHom_compos)
apply (rule conjI)
 apply ((rule ballI)+, simp add:compos_def compose_def,
        frule_tac x = x and y = y in Ring.ring_tOp_closed[of "A"], assumption+,
        simp)
apply (simp add:rHom_tOp)
 apply (frule_tac a = x in rHom_mem[of "f" "A" "B"], assumption+,
        frule_tac a = y in rHom_mem[of "f" "A" "B"], assumption+,
         simp add:rHom_tOp)
 apply (frule Ring.ring_one[of "A"], frule Ring.ring_one[of "B"],
        simp add:compos_def compose_def, simp add:rHom_one)
done

lemma rimg_ag:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow> aGroup (rimg A R f)"
apply (frule Ring.ring_is_ag [of "A"],
       frule Ring.ring_is_ag [of "R"])
apply (simp add:rHom_def, (erule conjE)+)
apply (subst aGroup_def)
apply (simp add:rimg_def)
apply (rule conjI)
 apply (rule Pi_I)+
 apply (simp add:image_def)
 apply (erule bexE)+
 apply simp
 apply (subst aHom_add [THEN sym, of "A" "R" "f"], assumption+)
 apply (blast dest: aGroup.ag_pOp_closed)
apply (rule conjI)
 apply ((rule allI, rule impI)+, simp add:image_def, (erule bexE)+, simp)
 apply (frule_tac x = x and y = xa in aGroup.ag_pOp_closed, assumption+,
        frule_tac x = xa and y = xb in aGroup.ag_pOp_closed, assumption+)
 apply (simp add:aHom_add[of "A" "R" "f", THEN sym] aGroup.ag_pOp_assoc)
apply (rule conjI)
 apply ((rule allI, rule impI)+, simp add:image_def, (erule bexE)+, simp)
 apply (simp add:aHom_add[of "A" "R" "f", THEN sym] aGroup.ag_pOp_commute)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:image_def, erule bexE, simp)
 apply (simp add:aHom_inv_inv[THEN sym],
        frule_tac x = xa in aGroup.ag_mOp_closed[of "A"], assumption+, blast)
apply (rule conjI)
  apply (rule allI, rule impI, simp add:image_def, (erule bexE)+, simp)
   apply (simp add:aHom_inv_inv[THEN sym],
        frule_tac x = x in aGroup.ag_mOp_closed[of "A"], assumption+,
        simp add:aHom_add[of "A" "R" "f", THEN sym])
 apply (simp add:aGroup.ag_l_inv1 aHom_0_0)
apply (rule conjI)
 apply (simp add:image_def)
 apply (frule aHom_0_0[THEN sym, of "A" "R" "f"], assumption+,
        frule Ring.ring_zero[of "A"], blast)

apply (rule allI, rule impI,
       simp add:image_def, erule bexE,
       frule_tac a = x in aHom_mem[of "A" "R" "f"], assumption+, simp)
 apply (simp add:aGroup.ag_l_zero)
done

lemma rimg_ring:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow> Ring (rimg A R f)"
apply (unfold Ring_def [of "rimg A R f"])
apply (frule rimg_ag[of "A" "R" "f"], assumption+)
 apply (rule conjI, simp add:aGroup_def[of "rimg A R f"])
apply(rule conjI)
 apply (rule conjI, rule allI, rule impI)
 apply (frule aGroup.ag_inc_zero[of "rimg A R f"],
        subst aGroup.ag_pOp_commute, assumption+,
        simp add:aGroup.ag_r_zero[of "rimg A R f"])

apply (rule conjI)
apply (rule Pi_I)+
apply (thin_tac "aGroup (rimg A R f)",
       simp add:rimg_def, simp add:image_def, (erule bexE)+,
       simp add:rHom_tOp[THEN sym])
 apply (blast dest:Ring.ring_tOp_closed)
 apply ((rule allI)+, (rule impI)+)
 apply (thin_tac "aGroup (rimg A R f)", simp add:rimg_def,
        simp add:image_def, (erule bexE)+, simp)
 apply (frule_tac x = x and y = xa in Ring.ring_tOp_closed, assumption+,
        frule_tac x = xa and y = xb in Ring.ring_tOp_closed, assumption+,
        simp add:rHom_tOp[THEN sym],
        simp add:Ring.ring_tOp_assoc)
apply (rule conjI, rule conjI, (rule allI)+, (rule impI)+)
 apply (thin_tac "aGroup (rimg A R f)", simp add:rimg_def,
        simp add:image_def, (erule bexE)+, simp,
        simp add:rHom_tOp[THEN sym],
        simp add:Ring.ring_tOp_commute)
  apply (thin_tac "aGroup (rimg A R f)", simp add:rimg_def,
         simp add:image_def)
  apply (subst rHom_one [THEN sym, of "A" "R" "f"], assumption+,
         frule Ring.ring_one[of "A"], blast)
apply (rule conjI, (rule allI)+, (rule impI)+)
apply (simp add:rimg_def, fold rimg_def,
       simp add:image_def, (erule bexE)+, simp)
 apply (frule rHom_aHom[of "f" "A" "R"],
        frule Ring.ring_is_ag [of "A"],
        frule Ring.ring_is_ag [of "R"],
        simp add:aHom_add[THEN sym],
        simp add:rHom_tOp[THEN sym])
 apply (frule_tac x = xa and y = xb in aGroup.ag_pOp_closed[of "A"],
          assumption+,
        frule_tac x = x and y = xa in Ring.ring_tOp_closed[of "A"],
          assumption+,
        frule_tac x = x and y = xb in Ring.ring_tOp_closed[of "A"],
          assumption+,
        simp add:aHom_add[THEN sym],
        simp add:rHom_tOp[THEN sym],
        simp add:Ring.ring_distrib1)
 apply (rule allI, rule impI,
        thin_tac "aGroup (rimg A R f)")
 apply (simp add:rimg_def,
        simp add:image_def, erule bexE, simp add:rHom_tOp[THEN sym],
        frule_tac a = x in rHom_mem[of "f" "A" "R"], assumption+,
         simp add:Ring.ring_l_one)
done

definition
  ideal :: "[_ , 'a set] \<Rightarrow> bool" where
  "ideal R I \<longleftrightarrow> (R +> I) \<and> (\<forall>r\<in>carrier R. \<forall>x\<in>I. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> x \<in> I))"


lemma (in Ring) ideal_asubg:"ideal R I \<Longrightarrow> R +> I"
by (simp add:ideal_def)

lemma (in Ring) ideal_pOp_closed:"\<lbrakk>ideal R I; x \<in> I; y \<in> I \<rbrakk>
                                                   \<Longrightarrow> x \<plusminus> y \<in> I"
apply (unfold ideal_def, frule conjunct1, fold ideal_def)
apply (cut_tac ring_is_ag,
       simp add:aGroup.asubg_pOp_closed)
done

lemma (in Ring) ideal_nsum_closedTr:"ideal R I \<Longrightarrow>
                                      (\<forall>j \<le> n. f j \<in> I) \<longrightarrow>  nsum R f n \<in> I"
apply (induct_tac n)
 apply (rule impI)
 apply simp

 apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (rule ideal_pOp_closed, assumption+)
 apply simp
done

lemma (in Ring) ideal_nsum_closed:"\<lbrakk>ideal R I; \<forall>j \<le> n. f j \<in> I\<rbrakk> \<Longrightarrow>
                                             nsum R f n \<in> I"
by (simp add:ideal_nsum_closedTr)

lemma (in Ring) ideal_subset1:"ideal R I \<Longrightarrow> I \<subseteq> carrier R"
apply (unfold ideal_def, frule conjunct1, fold ideal_def)
  apply (simp add:asubGroup_def sg_def, (erule conjE)+)
  apply (cut_tac ring_is_ag,
         simp add:aGroup.ag_carrier_carrier)
done

lemma (in Ring) ideal_subset:"\<lbrakk>ideal R I; h \<in> I\<rbrakk> \<Longrightarrow> h \<in> carrier R"
by (frule ideal_subset1[of "I"],
       simp add:subsetD)

lemma (in Ring) ideal_ring_multiple:"\<lbrakk>ideal R I; x \<in> I; r \<in> carrier R\<rbrakk> \<Longrightarrow>
       r \<cdot>\<^sub>r x \<in> I"
by (simp add:ideal_def)

lemma (in Ring) ideal_ring_multiple1:"\<lbrakk>ideal R I; x \<in> I; r \<in> carrier R \<rbrakk> \<Longrightarrow>
       x \<cdot>\<^sub>r r \<in> I"
apply (frule ideal_subset[of "I" "x"], assumption+)
apply (simp add:ring_tOp_commute ideal_ring_multiple)
done

lemma (in Ring) ideal_npow_closedTr:"\<lbrakk>ideal R I; x \<in> I\<rbrakk> \<Longrightarrow>
                                        0 < n \<longrightarrow> x^\<^bsup>R n\<^esup> \<in> I"
apply (induct_tac n,
       simp)
apply (rule impI)
 apply simp
 apply (case_tac "n = 0", simp)
 apply (frule ideal_subset[of "I" "x"], assumption+,
        simp add:ring_l_one)

 apply simp
apply (frule ideal_subset[of "I" "x"], assumption+,
       rule ideal_ring_multiple, assumption+,
       simp add:ideal_subset)
done

lemma (in Ring) ideal_npow_closed:"\<lbrakk>ideal R I; x \<in> I; 0 < n\<rbrakk> \<Longrightarrow> x^\<^bsup>R n\<^esup> \<in> I"
by (simp add:ideal_npow_closedTr)

lemma (in Ring) times_modTr:"\<lbrakk>a \<in> carrier R; a' \<in> carrier R; b \<in> carrier R;
 b' \<in> carrier R; ideal R I; a \<plusminus> (-\<^sub>a b) \<in> I; a' \<plusminus> (-\<^sub>a b') \<in> I\<rbrakk> \<Longrightarrow>
                           a \<cdot>\<^sub>r a' \<plusminus> (-\<^sub>a (b \<cdot>\<^sub>r b')) \<in> I"
apply (cut_tac ring_is_ag)
apply (subgoal_tac "a \<cdot>\<^sub>r a' \<plusminus> (-\<^sub>a (b \<cdot>\<^sub>r b')) = a \<cdot>\<^sub>r a' \<plusminus> (-\<^sub>a (a \<cdot>\<^sub>r b'))
                       \<plusminus> (a \<cdot>\<^sub>r b' \<plusminus> (-\<^sub>a (b \<cdot>\<^sub>r b')))")
apply simp
 apply (simp add:ring_inv1_2[of "a" "b'"], simp add:ring_inv1_1[of "b" "b'"])
 apply (frule aGroup.ag_mOp_closed[of "R" "b'"], assumption+)
 apply (simp add:ring_distrib1[THEN sym, of "a" "a'" "-\<^sub>a b'"])
 apply (frule aGroup.ag_mOp_closed[of "R" "b"], assumption+)
 apply (frule ring_distrib2[THEN sym, of "b'" "a" "-\<^sub>a b" ], assumption+)
 apply simp

apply (thin_tac "a \<cdot>\<^sub>r a' \<plusminus> (-\<^sub>a b) \<cdot>\<^sub>r b' = a \<cdot>\<^sub>r (a' \<plusminus> -\<^sub>a b') \<plusminus> (a \<plusminus> -\<^sub>a b) \<cdot>\<^sub>r b'",
       thin_tac "a \<cdot>\<^sub>r b' \<plusminus> (-\<^sub>a b) \<cdot>\<^sub>r b' = (a \<plusminus> -\<^sub>a b) \<cdot>\<^sub>r b'")
 apply (frule ideal_ring_multiple[of "I" "a' \<plusminus> (-\<^sub>a b')" "a"], assumption+,
        frule ideal_ring_multiple1[of "I" "a \<plusminus> (-\<^sub>a b)" "b'"], assumption+)
 apply (simp add:ideal_pOp_closed)

apply (frule ring_tOp_closed[of "a" "a'"], assumption+,
       frule ring_tOp_closed[of "a" "b'"], assumption+,
       frule ring_tOp_closed[of "b" "b'"], assumption+,
       frule aGroup.ag_mOp_closed[of "R" "b \<cdot>\<^sub>r b'"], assumption+,
       frule aGroup.ag_mOp_closed[of "R" "a \<cdot>\<^sub>r b'"], assumption+)

 apply (subst aGroup.ag_pOp_assoc[of "R"], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (simp add:aGroup.ag_pOp_assoc[THEN sym, of "R" "-\<^sub>a (a \<cdot>\<^sub>r b')" "a \<cdot>\<^sub>r b'"
                          "-\<^sub>a (b \<cdot>\<^sub>r b')"],
        simp add:aGroup.ag_l_inv1 aGroup.ag_l_zero)
done

lemma (in Ring) ideal_inv1_closed:"\<lbrakk> ideal R I; x \<in> I \<rbrakk> \<Longrightarrow> -\<^sub>a x \<in> I"
apply (cut_tac ring_is_ag)
apply (unfold ideal_def, frule conjunct1, fold ideal_def)
apply (simp add:aGroup.asubg_mOp_closed[of "R" "I"])
done

lemma (in Ring) ideal_zero:"ideal R I  \<Longrightarrow> \<zero> \<in> I"

apply (cut_tac ring_is_ag)
apply (unfold ideal_def, frule conjunct1, fold ideal_def)
apply (simp add:aGroup.asubg_inc_zero)
done

lemma (in Ring) ideal_zero_forall:"\<forall>I. ideal R I \<longrightarrow>  \<zero> \<in> I"
by (simp add:ideal_zero)

lemma (in Ring) ideal_ele_sumTr1:"\<lbrakk> ideal R I; a \<in> carrier R; b \<in> carrier R;
          a \<plusminus> b \<in> I; a \<in> I \<rbrakk> \<Longrightarrow> b \<in> I"
apply (frule ideal_inv1_closed[of "I" "a"], assumption+)
apply (frule ideal_pOp_closed[of "I" "-\<^sub>a a" "a \<plusminus> b"], assumption+)
apply (frule ideal_subset[of "I" "-\<^sub>a a"], assumption+)
apply (cut_tac ring_is_ag,
       simp add:aGroup.ag_pOp_assoc[THEN sym],
       simp add:aGroup.ag_l_inv1,
       simp add:aGroup.ag_l_zero)
done

lemma (in Ring) ideal_ele_sumTr2:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R;
                a \<plusminus> b \<in> I; b \<in> I\<rbrakk> \<Longrightarrow> a \<in> I"
apply (cut_tac ring_is_ag,
       simp add:aGroup.ag_pOp_commute[of "R" "a" "b"])
apply (simp add:ideal_ele_sumTr1[of "I" "b" "a"])
done

lemma (in Ring) ideal_condition:"\<lbrakk>I \<subseteq> carrier R; I \<noteq> {};
       \<forall>x\<in>I. \<forall>y\<in>I. x \<plusminus> (-\<^sub>a y) \<in> I; \<forall>r\<in>carrier R. \<forall>x\<in>I. r \<cdot>\<^sub>r x \<in> I \<rbrakk> \<Longrightarrow>
                                   ideal R I"
apply (simp add:ideal_def)
 apply (cut_tac ring_is_ag)
 apply (rule aGroup.asubg_test[of "R" "I"], assumption+)
done

lemma (in Ring) ideal_condition1:"\<lbrakk>I \<subseteq> carrier R; I \<noteq> {};
  \<forall>x\<in>I. \<forall>y\<in>I. x \<plusminus> y \<in> I; \<forall>r\<in>carrier R. \<forall>x\<in>I. r \<cdot>\<^sub>r x \<in> I \<rbrakk> \<Longrightarrow> ideal R I"
apply (rule ideal_condition[of "I"], assumption+)
apply (rule ballI)+
apply (cut_tac ring_is_ag,
       cut_tac ring_one,
       frule aGroup.ag_mOp_closed[of "R" "1\<^sub>r"], assumption+)
 apply (frule_tac x = "-\<^sub>a 1\<^sub>r " in bspec, assumption+,
        thin_tac "\<forall>r\<in>carrier R. \<forall>x\<in>I. r \<cdot>\<^sub>r x \<in> I",
        rotate_tac -1,
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>x\<in>I. (-\<^sub>a 1\<^sub>r) \<cdot>\<^sub>r x \<in> I")
 apply (frule_tac c = y in subsetD[of "I" "carrier R"], assumption+,
        simp add:ring_times_minusl[THEN sym], simp add:ideal_pOp_closed)
done

lemma (in Ring) zero_ideal:"ideal R {\<zero>}"
apply (cut_tac ring_is_ag)
apply (rule ideal_condition1)
 apply (simp add:ring_zero)
 apply simp
 apply simp
apply (cut_tac ring_zero, simp add:aGroup.ag_l_zero)
apply simp
 apply (rule ballI, simp add:ring_times_x_0)
done

lemma (in Ring) whole_ideal:"ideal R (carrier R)"
apply (rule ideal_condition1)
 apply simp
 apply (cut_tac ring_zero, blast)
 apply (cut_tac ring_is_ag,
        simp add:aGroup.ag_pOp_closed,
        simp add:ring_tOp_closed)
done

lemma (in Ring) ideal_inc_one:"\<lbrakk>ideal R I; 1\<^sub>r \<in> I \<rbrakk> \<Longrightarrow> I = carrier R"
apply (rule equalityI)
apply (simp add:ideal_subset1)
apply (rule subsetI,
       frule_tac r = x in ideal_ring_multiple[of "I" "1\<^sub>r"], assumption+,
       simp add:ring_r_one)
done

lemma (in Ring) ideal_inc_one1:"ideal R I \<Longrightarrow>
                              (1\<^sub>r \<in> I) = (I = carrier R)"
apply (rule iffI)
 apply (simp add:ideal_inc_one)
 apply (frule sym, thin_tac "I = carrier R",
        cut_tac ring_one, simp)
done

definition
  Unit :: "_ \<Rightarrow> 'a \<Rightarrow> bool" where
  "Unit R a \<longleftrightarrow> a \<in> carrier R \<and> (\<exists>b\<in>carrier R. a \<cdot>\<^sub>r\<^bsub>R\<^esub> b = 1\<^sub>r\<^bsub>R\<^esub>)"

lemma (in Ring) ideal_inc_unit:"\<lbrakk>ideal R I; a \<in> I; Unit R a\<rbrakk> \<Longrightarrow> 1\<^sub>r \<in> I"
by (simp add:Unit_def, erule conjE, erule bexE,
       frule_tac r = b in ideal_ring_multiple1[of "I" "a"], assumption+,
       simp)

lemma (in Ring) proper_ideal:"\<lbrakk>ideal R I; 1\<^sub>r \<notin> I\<rbrakk> \<Longrightarrow> I \<noteq> carrier R"
apply (rule contrapos_pp, simp+)
apply (simp add: ring_one)
done

lemma (in Ring) ideal_inc_unit1:"\<lbrakk>a \<in> carrier R; Unit R a; ideal R I; a \<in> I\<rbrakk>
                        \<Longrightarrow> I = carrier R"
apply (frule ideal_inc_unit[of "I" "a"], assumption+)
apply (rule ideal_inc_one[of "I"], assumption+)
done

lemma (in Ring) int_ideal:"\<lbrakk>ideal R I; ideal R J\<rbrakk> \<Longrightarrow> ideal R (I \<inter> J)"
apply (rule ideal_condition1)
apply (frule ideal_subset1[of "I"], frule ideal_subset1[of "J"])
 apply blast
 apply (frule ideal_zero[of "I"], frule ideal_zero[of "J"], blast)

 apply ((rule ballI)+, simp, (erule conjE)+,
         simp add:ideal_pOp_closed)
 apply ((rule ballI)+, simp, (erule conjE)+)
 apply (simp add:ideal_ring_multiple)
done

definition
  ideal_prod::"[_, 'a set, 'a set] \<Rightarrow> 'a set" (infix "\<diamondsuit>\<^sub>r\<index>" 90 ) where
  "ideal_prod R I J == \<Inter> {L. ideal R L \<and>
                              {x.(\<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r\<^bsub>R\<^esub> j)} \<subseteq> L}"

lemma (in Ring) set_sum_mem:"\<lbrakk>a \<in> I; b \<in> J; I \<subseteq> carrier R; J \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
             a \<plusminus> b \<in> I \<minusplus> J"
apply (cut_tac ring_is_ag)
apply (simp add:aGroup.set_sum, blast)
done

lemma (in Ring) sum_ideals:"\<lbrakk>ideal R I1; ideal R I2\<rbrakk> \<Longrightarrow> ideal R (I1 \<minusplus> I2)"
apply (cut_tac ring_is_ag)
apply (frule ideal_subset1[of "I1"], frule ideal_subset1[of "I2"])
apply (rule ideal_condition1)
 apply (rule subsetI, simp add:aGroup.set_sum, (erule bexE)+)
 apply (frule_tac h = h in ideal_subset[of "I1"], assumption+,
        frule_tac h = k in ideal_subset[of "I2"], assumption+,
        cut_tac ring_is_ag,
        simp add:aGroup.ag_pOp_closed)
 apply (frule ideal_zero[of "I1"], frule ideal_zero[of "I2"],
        frule set_sum_mem[of "\<zero>" "I1" "\<zero>" "I2"], assumption+, blast)
apply (rule ballI)+
 apply (simp add:aGroup.set_sum, (erule bexE)+, simp)
 apply (rename_tac x y i ia j ja)
 apply (frule_tac h = i in ideal_subset[of "I1"], assumption+,
        frule_tac h = ia in ideal_subset[of "I1"], assumption+,
        frule_tac h = j in ideal_subset[of "I2"], assumption+,
        frule_tac h = ja in ideal_subset[of "I2"], assumption+)
 apply (subst aGroup.pOp_assocTr43, assumption+)
 apply (frule_tac x = j and y = ia in aGroup.ag_pOp_commute[of "R"],
          assumption+, simp)
 apply (subst aGroup.pOp_assocTr43[THEN sym], assumption+)
 apply (frule_tac x = i and y = ia in ideal_pOp_closed[of "I1"], assumption+,
        frule_tac x = j and y = ja in ideal_pOp_closed[of "I2"], assumption+,
        blast)
apply (rule ballI)+
 apply (simp add:aGroup.set_sum, (erule bexE)+, simp)
 apply (rename_tac r x i j)
 apply (frule_tac h = i in ideal_subset[of "I1"], assumption+,
        frule_tac h = j in ideal_subset[of "I2"], assumption+)
 apply (simp add:ring_distrib1)
 apply (frule_tac x = i and r = r in ideal_ring_multiple[of "I1"], assumption+,
        frule_tac x = j and r = r in ideal_ring_multiple[of "I2"], assumption+,
        blast)
done

lemma (in Ring) sum_ideals_la1:"\<lbrakk>ideal R I1; ideal R I2\<rbrakk> \<Longrightarrow> I1 \<subseteq> (I1 \<minusplus> I2)"
apply (cut_tac ring_is_ag)
apply (rule subsetI)
apply (frule ideal_zero[of "I2"],
       frule_tac h = x in ideal_subset[of "I1"], assumption+,
       frule_tac x = x in aGroup.ag_r_zero[of "R"], assumption+)
apply (subst aGroup.set_sum, assumption,
       simp add:ideal_subset1, simp add:ideal_subset1, simp,
       frule sym, thin_tac "x \<plusminus> \<zero> = x", blast)
done

lemma (in Ring) sum_ideals_la2:"\<lbrakk>ideal R I1; ideal R I2 \<rbrakk> \<Longrightarrow> I2 \<subseteq> (I1 \<minusplus> I2)"
apply (cut_tac ring_is_ag)
apply (rule subsetI)
apply (frule ideal_zero[of "I1"],
       frule_tac h = x in ideal_subset[of "I2"], assumption+,
       frule_tac x = x in aGroup.ag_l_zero[of "R"], assumption+)
apply (subst aGroup.set_sum, assumption,
       simp add:ideal_subset1, simp add:ideal_subset1, simp,
       frule sym, thin_tac "\<zero> \<plusminus> x = x", blast)
done

lemma (in Ring) sum_ideals_cont:"\<lbrakk>ideal R I;  A \<subseteq> I; B \<subseteq> I \<rbrakk> \<Longrightarrow> A \<minusplus> B \<subseteq> I"
apply (cut_tac ring_is_ag)
apply (rule subsetI)
 apply (frule ideal_subset1[of I],
        frule subset_trans[of A I "carrier R"], assumption+,
        frule subset_trans[of B I "carrier R"], assumption+)
 apply (simp add:aGroup.set_sum[of R], (erule bexE)+, simp)
 apply (frule_tac c = h in subsetD[of "A" "I"], assumption+,
        frule_tac c = k in subsetD[of "B" "I"], assumption+)
 apply (simp add:ideal_pOp_closed)
done

lemma (in Ring) ideals_set_sum:"\<lbrakk>ideal R A; ideal R B; x \<in> A \<minusplus> B\<rbrakk> \<Longrightarrow>
             \<exists>h\<in>A. \<exists>k\<in>B. x = h \<plusminus> k"
apply (frule ideal_subset1[of A],
       frule ideal_subset1[of B])
apply (cut_tac ring_is_ag,
       simp add:aGroup.set_sum)
done

definition
  Rxa :: "[_, 'a ] \<Rightarrow> 'a set" (infixl "\<diamondsuit>\<^sub>p" 200)  where
  "Rxa R a = {x. \<exists>r\<in>carrier R. x = (r \<cdot>\<^sub>r\<^bsub>R\<^esub> a)}"

lemma (in Ring) a_in_principal:"a \<in> carrier R \<Longrightarrow> a \<in> Rxa R a"
apply (cut_tac ring_one,
       frule ring_l_one[THEN sym, of "a"])
apply (simp add:Rxa_def, blast)
done

lemma (in Ring) principal_ideal:"a \<in> carrier R \<Longrightarrow> ideal R (Rxa R a)"
apply (rule ideal_condition1)
  apply (rule subsetI,
         simp add:Rxa_def, erule bexE, simp add:ring_tOp_closed)
apply (frule a_in_principal[of "a"], blast)
apply ((rule ballI)+,
        simp add:Rxa_def, (erule bexE)+, simp,
        subst ring_distrib2[THEN sym], assumption+,
        cut_tac ring_is_ag,
        frule_tac x = r and y = ra in aGroup.ag_pOp_closed, assumption+,
        blast)
apply ((rule ballI)+,
        simp add:Rxa_def, (erule bexE)+, simp,
        simp add:ring_tOp_assoc[THEN sym])
 apply (frule_tac x = r and y = ra in ring_tOp_closed, assumption, blast)
done

lemma (in Ring) rxa_in_Rxa:"\<lbrakk>a \<in> carrier R; r \<in> carrier R\<rbrakk> \<Longrightarrow>
                                     r \<cdot>\<^sub>r a \<in> Rxa R a"
by (simp add:Rxa_def, blast)

lemma (in Ring) Rxa_one:"Rxa R 1\<^sub>r = carrier R"
apply (rule equalityI)
 apply (rule subsetI, simp add:Rxa_def, erule bexE)
 apply (simp add:ring_r_one)

 apply (rule subsetI, simp add:Rxa_def)
 apply (frule_tac t = x in ring_r_one[THEN sym], blast)
done

lemma (in Ring) Rxa_zero:"Rxa R \<zero> = {\<zero>}"
apply (rule equalityI)
apply (rule subsetI)
 apply (simp add:Rxa_def, erule bexE, simp add:ring_times_x_0)
apply (rule subsetI)
 apply (simp add:Rxa_def)
 apply (cut_tac ring_zero,
        frule ring_times_x_0[THEN sym, of "\<zero>"], blast)
done

lemma (in Ring) Rxa_nonzero:"\<lbrakk>a \<in> carrier R; a \<noteq> \<zero>\<rbrakk> \<Longrightarrow> Rxa R a \<noteq> {\<zero>}"
apply (rule contrapos_pp, simp+)
 apply (frule a_in_principal[of "a"])
 apply simp
done

lemma (in Ring) ideal_cont_Rxa:"\<lbrakk>ideal R I; a \<in> I\<rbrakk> \<Longrightarrow> Rxa R a \<subseteq> I"
apply (rule subsetI)
 apply (simp add:Rxa_def, erule bexE, simp)
 apply (simp add:ideal_ring_multiple)
done

lemma (in Ring) Rxa_mult_smaller:"\<lbrakk> a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
                    Rxa R (a \<cdot>\<^sub>r b) \<subseteq> Rxa R b"
apply (frule rxa_in_Rxa[of b a], assumption,
       frule principal_ideal[of b])
apply (rule ideal_cont_Rxa[of "R \<diamondsuit>\<^sub>p b" "a \<cdot>\<^sub>r b"], assumption+)
done

lemma (in Ring) id_ideal_psub_sum:"\<lbrakk>ideal R I; a \<in> carrier R; a \<notin> I\<rbrakk> \<Longrightarrow>
                                             I \<subset> I \<minusplus> Rxa R a"
apply (cut_tac ring_is_ag)
apply (simp add:psubset_eq)
apply (frule principal_ideal)
apply (rule conjI)
apply (rule sum_ideals_la1, assumption+)
apply (rule contrapos_pp) apply simp+
apply (frule sum_ideals_la2[of "I" "Rxa R a"], assumption+)
apply (frule a_in_principal[of "a"],
       frule subsetD[of "Rxa R a" "I \<minusplus> Rxa R a" "a"], assumption+)
apply simp
done

lemma (in Ring) mul_two_principal_idealsTr:"\<lbrakk>a \<in> carrier R; b \<in> carrier R;
         x \<in> Rxa R a; y \<in> Rxa R b\<rbrakk> \<Longrightarrow> \<exists>r\<in>carrier R. x \<cdot>\<^sub>r y = r \<cdot>\<^sub>r (a \<cdot>\<^sub>r b)"
apply (simp add:Rxa_def, (erule bexE)+)
apply simp
apply (frule_tac x = ra and y = b in ring_tOp_closed, assumption+)
apply (simp add:ring_tOp_assoc)
apply (simp add:ring_tOp_assoc[THEN sym, of a _ b])
apply (simp add:ring_tOp_commute[of a], simp add:ring_tOp_assoc)
apply (frule_tac x = a and y = b in ring_tOp_closed, assumption+,
       thin_tac "ra \<cdot>\<^sub>r b \<in> carrier R",
       simp add:ring_tOp_assoc[THEN sym, of _ _ "a \<cdot>\<^sub>r b"],
       frule_tac x = r and y = ra in ring_tOp_closed, assumption+)
apply (simp add:ring_tOp_commute[of b a])
apply blast
done


primrec sum_pr_ideals::"[('a, 'm) Ring_scheme, nat \<Rightarrow> 'a, nat] \<Rightarrow> 'a set"
where
  sum_pr0: "sum_pr_ideals R f 0 = Rxa R (f 0)"
| sum_prn: "sum_pr_ideals R f (Suc n) =
                  (Rxa R (f (Suc n))) \<minusplus>\<^bsub>R\<^esub> (sum_pr_ideals R f n)"

lemma (in Ring) sum_of_prideals0:
      "\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<longrightarrow> ideal R (sum_pr_ideals R f n)"
apply (induct_tac n)
apply (rule allI) apply (rule impI)
 apply simp
 apply (rule Ring.principal_ideal, rule Ring_axioms, assumption)
(** case n **)
apply (rule allI, rule impI)
 apply (frule_tac x = f in spec,
        thin_tac "\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<longrightarrow>
               ideal R (sum_pr_ideals R f n)")
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (cut_tac a = "f (Suc n)" in  principal_ideal,
       simp)
 apply (rule_tac ?I1.0 = "Rxa R (f (Suc n))" and
        ?I2.0 = "sum_pr_ideals R f n" in Ring.sum_ideals, rule Ring_axioms, assumption+)
done

lemma (in Ring) sum_of_prideals:"\<lbrakk>\<forall>l \<le> n. f l \<in> carrier R\<rbrakk> \<Longrightarrow>
                      ideal R (sum_pr_ideals R f n)"
apply (simp add:sum_of_prideals0)
done

text \<open>later, we show \<open>sum_pr_ideals\<close> is the least ideal containing
        \<open>{f 0, f 1,\<dots>, f n}\<close>\<close>

lemma (in Ring) sum_of_prideals1:"\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<longrightarrow>
                                    f ` {i. i \<le> n} \<subseteq> (sum_pr_ideals R f n)"
apply (induct_tac n)
 apply (rule allI, rule impI)
apply (simp, simp add:a_in_principal)

apply (rule allI, rule impI)
 apply (frule_tac a = f in forall_spec,
        thin_tac "\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<longrightarrow>
               f ` {i. i \<le> n} \<subseteq> sum_pr_ideals R f n")
 apply (rule allI, cut_tac n = n in Nset_un, simp)

 apply (subst Nset_un)
 apply (cut_tac A = "{i. i \<le> (Suc n)}" and f = f and B = "carrier R" and
        ?A1.0 = "{i. i \<le> n}" and ?A2.0 = "{Suc n}" in im_set_un1,
        simp, rule Nset_un)
 apply (thin_tac "\<forall>f. (\<forall>l\<le>n. f l \<in> carrier R) \<longrightarrow>
               f ` {i. i \<le> n} \<subseteq> sum_pr_ideals R f n",
        simp)
 apply (cut_tac n = n and f = f in sum_of_prideals,
        cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (cut_tac a = "f (Suc n)" in principal_ideal, simp)
 apply (frule_tac ?I1.0 = "Rxa R (f (Suc n))" and ?I2.0 = "sum_pr_ideals R f n"
                 in sum_ideals_la1, assumption+,
        cut_tac a = "f (Suc n)" in a_in_principal, simp,
        frule_tac A = "R \<diamondsuit>\<^sub>p f (Suc n)" and
         B = "R \<diamondsuit>\<^sub>p f (Suc n) \<minusplus> sum_pr_ideals R f n" and c = "f (Suc n)" in
         subsetD, simp+)
  apply (frule_tac ?I1.0 = "Rxa R (f (Suc n))" and
         ?I2.0 = "sum_pr_ideals R f n" in sum_ideals_la2, assumption+)
  apply (rule_tac A = "f ` {j. j \<le> n}" and B = "sum_pr_ideals R f n" and
         C = "Rxa R (f (Suc n)) \<minusplus> sum_pr_ideals R f n" in subset_trans,
         assumption+)
done

lemma (in Ring) sum_of_prideals2:"\<forall>l \<le> n. f l \<in> carrier R
               \<Longrightarrow>  f ` {i. i \<le> n} \<subseteq> (sum_pr_ideals R f n)"
apply (simp add:sum_of_prideals1)
done

lemma (in Ring) sum_of_prideals3:"ideal R I \<Longrightarrow>
      \<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<and> (f ` {i. i \<le> n} \<subseteq> I) \<longrightarrow>
          (sum_pr_ideals R f n \<subseteq> I)"
apply (induct_tac n)
 apply (rule allI, rule impI, erule conjE)
 apply simp
 apply (rule ideal_cont_Rxa[of I], assumption+)

apply (rule allI, rule impI, erule conjE)
 apply (frule_tac a = f in forall_spec,
        thin_tac "\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<and> f `{i. i \<le> n} \<subseteq> I \<longrightarrow>
               sum_pr_ideals R f n \<subseteq> I")
 apply (simp add:Nset_un)
 apply (thin_tac "\<forall>f. (\<forall>l \<le> n. f l \<in> carrier R) \<and> f ` {i. i \<le> n} \<subseteq> I \<longrightarrow>
               sum_pr_ideals R f n \<subseteq> I")
 apply (frule_tac x = "Suc n" in spec,
        thin_tac "\<forall>l \<le> (Suc n). f l \<in> carrier R", simp)
   apply (cut_tac a = "Suc n" and A = "{i. i \<le> Suc n}" and
          f = f in mem_in_image2, simp)
   apply (frule_tac A = "f ` {i. i \<le> Suc n}" and B = I and c = "f (Suc n)" in
          subsetD,  assumption+)
 apply (rule_tac A = "Rxa R  (f (Suc n))" and B = "sum_pr_ideals R f n" in
        sum_ideals_cont[of I], assumption)
 apply (rule ideal_cont_Rxa[of I], assumption+)
done

lemma (in Ring) sum_of_prideals4:"\<lbrakk>ideal R I; \<forall>l \<le> n. f l \<in> carrier R;
       (f ` {i. i \<le> n} \<subseteq> I)\<rbrakk> \<Longrightarrow> sum_pr_ideals R f n \<subseteq> I"
apply (simp add:sum_of_prideals3)
done

lemma ker_ideal:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow> ideal A (ker\<^bsub>A,R\<^esub> f)"
apply (frule Ring.ring_is_ag[of "A"], frule Ring.ring_is_ag[of "R"])
apply (rule Ring.ideal_condition1, assumption+)
apply (rule subsetI,
       simp add:ker_def)
apply (simp add:rHom_def, frule conjunct1)
apply (frule ker_inc_zero[of "A" "R" "f"], assumption+, blast)

apply (rule ballI)+
 apply (simp add:ker_def, (erule conjE)+)
 apply (simp add:aGroup.ag_pOp_closed)
 apply (simp add:rHom_def, frule conjunct1,
        simp add:aHom_add,
        frule Ring.ring_zero[of "R"],
        simp add:aGroup.ag_l_zero)
apply (rule ballI)+
 apply (simp add:ker_def, (erule conjE)+)
 apply (simp add:Ring.ring_tOp_closed)
 apply (simp add:rHom_tOp)
 apply (frule_tac a = r in rHom_mem[of "f" "A" "R"], assumption+,
        simp add:Ring.ring_times_x_0)
done

subsection "Ring of integers"

definition
  Zr :: "int Ring" where
  "Zr = \<lparr> carrier = Zset, pop = \<lambda>n\<in>Zset. \<lambda>m\<in>Zset. (m + n),
    mop = \<lambda>l\<in>Zset. -l, zero = 0, tp = \<lambda>m\<in>Zset. \<lambda>n\<in>Zset. m * n, un = 1\<rparr>"

lemma ring_of_integers:"Ring Zr"
apply (simp add:Ring_def)
apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:Zr_def Zset_def)
apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule conjI,
       rule allI, rule impI, simp add:Zr_def Zset_def)
apply (rule conjI, simp add:Zr_def Zset_def)
apply (rule conjI,
       rule allI, rule impI, simp add:Zr_def Zset_def)
apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule conjI,
       (rule allI, rule impI)+, simp add:Zr_def Zset_def)
apply (rule conjI,
       (rule allI, rule impI)+, simp add:Zr_def Zset_def)
apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule conjI,
       (rule allI, rule impI)+, simp add:Zr_def Zset_def)
 apply (simp add: distrib_left)
apply (rule allI, rule impI)
  apply (simp add:Zr_def Zset_def)
done

lemma Zr_zero:"\<zero>\<^bsub>Zr\<^esub> = 0"
by (simp add:Zr_def)

lemma Zr_one:"1\<^sub>r\<^bsub>Zr\<^esub> = 1"
by (simp add:Zr_def)

lemma Zr_minus:"-\<^sub>a\<^bsub>Zr\<^esub> n = - n"
by (simp add:Zr_def Zset_def)

lemma Zr_add:"n \<plusminus>\<^bsub>Zr\<^esub> m = n + m"
by (simp add:Zr_def Zset_def)

lemma Zr_times:"n \<cdot>\<^sub>r\<^bsub>Zr\<^esub> m = n * m"
by (simp add:Zr_def Zset_def)

definition
  lev :: "int set \<Rightarrow> int" where
  "lev I = Zleast {n. n \<in> I \<and> 0 < n}"

lemma Zr_gen_Zleast:"\<lbrakk>ideal Zr I; I \<noteq> {0::int}\<rbrakk> \<Longrightarrow>
                       Rxa Zr (lev I) = I"
 apply (cut_tac ring_of_integers)
 apply (simp add:lev_def)
 apply (subgoal_tac "{n. n \<in> I \<and> 0 < n} \<noteq> {}")
 apply (subgoal_tac "{n. n \<in> I \<and> 0 < n} \<subseteq> Zset")
 apply (subgoal_tac "LB {n. n \<in> I \<and> 0 < n} 0")
 apply (frule_tac A = "{n. n \<in> I \<and> 0 < n}" and n = 0 in Zleast, assumption+)
 apply (erule conjE)+
 apply (fold lev_def)
defer
 apply (simp add:LB_def)
 apply (simp add:Zset_def)
 apply (frule Ring.ideal_zero[of "Zr" "I"], assumption+, simp add:Zr_zero)
 apply (frule singleton_sub[of "0" "I"])
 apply (frule sets_not_eq[of "I" "{0}"], assumption+, erule bexE, simp)
 apply (case_tac "0 < a", blast)
 apply (frule Ring.ring_one[of "Zr"])
 apply (frule Ring.ring_is_ag[of "Zr"],
         frule aGroup.ag_mOp_closed[of "Zr" "1\<^sub>r\<^bsub>Zr\<^esub>"], assumption)
 apply (frule_tac x = a in Ring.ideal_ring_multiple[of "Zr" "I" _ "-\<^sub>a\<^bsub>Zr\<^esub> 1\<^sub>r\<^bsub>Zr\<^esub>"],
        assumption+)
 apply (simp add:Zr_one Zr_minus,
        thin_tac "ideal Zr I", thin_tac "Ring Zr", thin_tac "1 \<in> carrier Zr",
        thin_tac "-1 \<in> carrier Zr", thin_tac "aGroup Zr")
 apply (simp add:Zr_def Zset_def)
 apply (subgoal_tac "0 < - a", blast)
 apply arith
 apply (thin_tac "{n \<in> I. 0 < n} \<noteq> {}", thin_tac "{n \<in> I. 0 < n} \<subseteq> Zset",
        thin_tac "LB {n \<in> I. 0 < n} 0")

apply simp
 apply (erule conjE)
 apply (frule Ring.ideal_cont_Rxa[of "Zr" "I" "lev I"], assumption+)
 apply (rule equalityI, assumption,
        thin_tac "Rxa Zr (lev I) \<subseteq> I")
 apply (rule subsetI)
  apply (simp add:Rxa_def, simp add:Zr_times)
 apply (cut_tac t = x and b = "lev I" in mult_div_mod_eq [symmetric])
 apply (subgoal_tac "x = (x div lev I) * (lev I)",
        subgoal_tac "x div lev I \<in> carrier Zr", blast)
 apply (simp add:Zr_def Zset_def)
apply (subgoal_tac "x mod lev I = 0", simp)
 apply (subst mult.commute, assumption)
 apply (subgoal_tac "x mod lev I \<in> I")
 apply (thin_tac "x = lev I * (x div lev I) + x mod lev I")
 apply (frule_tac a = x in pos_mod_conj[of "lev I"])
 apply (rule contrapos_pp, simp+)
 apply (erule conjE)
 apply (frule_tac a = "x mod (lev I)" in forall_spec)
  apply simp apply arith
  apply (frule_tac r = "x div (lev I)" in
          Ring.ideal_ring_multiple1[of "Zr" "I" "lev I"], assumption+,
          simp add:Zr_def Zset_def)
  apply (frule sym, thin_tac "x = lev I * (x div lev I) + x mod lev I")
  apply (rule_tac a = "lev I * (x div lev I)" and b = "x mod lev I " in
         Ring.ideal_ele_sumTr1[of "Zr" "I"], assumption+)
 apply (simp add:Zr_def Zset_def)
 apply (simp add:Zr_def Zset_def)
 apply (subst Zr_add)
 apply simp
 apply (simp add:Zr_times)
done

lemma Zr_pir:"ideal Zr I \<Longrightarrow> \<exists>n. Rxa Zr n = I" (** principal ideal ring *)
apply (case_tac "I = {(0::int)}")
 apply (subgoal_tac "Rxa Zr 0 = I") apply blast
 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Rxa_def)
 apply (simp add:Zr_def Zset_def)
 apply (rule subsetI)
 apply (simp add:Rxa_def Zr_def Zset_def)
apply (frule Zr_gen_Zleast [of "I"], assumption+)
 apply blast
done

section "Quotient rings"

lemma (in Ring) mem_set_ar_cos:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                                         a \<uplus>\<^bsub>R\<^esub> I \<in> set_ar_cos R I"
by (simp add:set_ar_cos_def, blast)

lemma (in Ring) I_in_set_ar_cos:"ideal R I \<Longrightarrow> I \<in> set_ar_cos R I"
apply (cut_tac ring_is_ag,
       frule ideal_asubg[of "I"],
       rule aGroup.unit_in_set_ar_cos, assumption+)
done

lemma (in Ring) ar_coset_same1:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R;
       b \<plusminus> (-\<^sub>a a) \<in> I \<rbrakk> \<Longrightarrow> a \<uplus>\<^bsub>R\<^esub> I = b \<uplus>\<^bsub>R\<^esub> I"
apply (cut_tac ring_is_ag)
 apply (frule aGroup.b_ag_group[of "R"])
 apply (simp add:ideal_def asubGroup_def) apply (erule conjE)
 apply (frule aGroup.ag_carrier_carrier[THEN sym, of "R"])
 apply simp
 apply (frule Group.rcs_eq[of "b_ag R" "I" "a" "b"], assumption+)
 apply (frule aGroup.agop_gop [of "R"])
 apply (frule aGroup.agiop_giop[of "R"]) apply simp
 apply (simp add:ar_coset_def rcs_def)
done

lemma (in Ring) ar_coset_same2:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R;
                                  a \<uplus>\<^bsub>R\<^esub> I = b \<uplus>\<^bsub>R\<^esub> I\<rbrakk> \<Longrightarrow>  b \<plusminus> (-\<^sub>a a) \<in> I"
apply (cut_tac ring_is_ag)
apply (simp add:ar_coset_def)
 apply (frule aGroup.b_ag_group[of "R"])
 apply (simp add:ideal_def asubGroup_def, frule conjunct1, fold asubGroup_def,
        fold ideal_def, simp add:asubGroup_def)
 apply (subgoal_tac "a \<in> carrier (b_ag R)",
         subgoal_tac "b \<in> carrier (b_ag R)")
 apply (simp add:Group.rcs_eq[THEN sym, of "b_ag R" "I" "a" "b"])
 apply (frule aGroup.agop_gop [of "R"])
 apply (frule aGroup.agiop_giop[of "R"]) apply simp
 apply (simp add:b_ag_def)+
done

lemma (in Ring) ar_coset_same3:"\<lbrakk>ideal R I; a \<in> carrier R; a \<uplus>\<^bsub>R\<^esub> I = I\<rbrakk> \<Longrightarrow>
                               a\<in>I"
apply (cut_tac ring_is_ag)
apply (simp add:ar_coset_def)
apply (rule Group.rcs_fixed [of "b_ag R" "I" "a" ])
apply (rule aGroup.b_ag_group, assumption)
apply (simp add:ideal_def asubGroup_def)
apply (simp add:b_ag_def)
apply assumption
done

lemma (in Ring) ar_coset_same3_1:"\<lbrakk>ideal R I; a \<in> carrier R; a \<notin> I\<rbrakk> \<Longrightarrow>
                                                    a \<uplus>\<^bsub>R\<^esub> I \<noteq> I"
apply (rule contrapos_pp, simp+)
apply (simp add:ar_coset_same3)
done

lemma (in Ring) ar_coset_same4:"\<lbrakk>ideal R I; a \<in> I\<rbrakk> \<Longrightarrow>
                                     a \<uplus>\<^bsub>R\<^esub> I = I"
apply (cut_tac ring_is_ag)
apply (frule ideal_subset[of "I" "a"], assumption+)
apply (simp add:ar_coset_def)
apply (rule Group.rcs_Unit2 [of "b_ag R" "I""a"])
apply (rule aGroup.b_ag_group, assumption)
apply (simp add:ideal_def asubGroup_def)
apply assumption
done

lemma (in Ring) ar_coset_same4_1:"\<lbrakk>ideal R I; a \<uplus>\<^bsub>R\<^esub> I \<noteq> I\<rbrakk> \<Longrightarrow> a \<notin> I"
apply (rule contrapos_pp, simp+)
apply (simp add:ar_coset_same4)
done

lemma (in Ring) belong_ar_coset1:"\<lbrakk>ideal R I; a \<in> carrier R; x \<in> carrier R;
                 x \<plusminus> (-\<^sub>a a) \<in> I\<rbrakk> \<Longrightarrow>  x \<in> a \<uplus>\<^bsub>R\<^esub> I"
apply (frule ar_coset_same1 [of "I" "a" "x"], assumption+)
apply (subgoal_tac "x \<in> x \<uplus>\<^bsub>R\<^esub> I")
 apply simp
 apply (cut_tac ring_is_ag)
 apply (subgoal_tac "carrier R = carrier (b_ag R)")
 apply (frule aGroup.agop_gop[THEN sym, of "R"])
 apply (frule aGroup.agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubGroup_def)

apply (rule Group.a_in_rcs [of "b_ag R" "I" "x"])
 apply (simp add: aGroup.b_ag_group)
 apply simp
 apply simp
 apply (simp add:b_ag_def)
done

lemma (in Ring) a_in_ar_coset:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow> a \<in> a \<uplus>\<^bsub>R\<^esub> I"
apply (rule belong_ar_coset1, assumption+)
apply (cut_tac ring_is_ag)
apply (simp add:aGroup.ag_r_inv1)
apply (simp add:ideal_zero)
done

lemma (in Ring) ar_coset_subsetD:"\<lbrakk>ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^bsub>R\<^esub> I \<rbrakk> \<Longrightarrow>
                           x \<in> carrier R"
 apply (subgoal_tac "carrier R = carrier (b_ag R)")
 apply (cut_tac ring_is_ag)
 apply (frule aGroup.agop_gop [THEN sym, of "R"])
 apply (frule aGroup.agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubGroup_def)
apply (rule Group.rcs_subset_elem[of "b_ag R" "I" "a" "x"])
 apply (simp add:aGroup.b_ag_group)
 apply simp
 apply assumption+
 apply (simp add:b_ag_def)
done

lemma (in Ring) ar_cos_mem:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                                 a \<uplus>\<^bsub>R\<^esub> I \<in> set_rcs (b_ag R) I"
apply (cut_tac ring_is_ag)
 apply (simp add:set_rcs_def ar_coset_def)
 apply (frule aGroup.ag_carrier_carrier[THEN sym, of "R"]) apply simp
 apply blast
done

lemma (in Ring) mem_ar_coset1:"\<lbrakk>ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^bsub>R\<^esub> I\<rbrakk> \<Longrightarrow>
                                 \<exists>h\<in>I. h \<plusminus> a = x"
 apply (cut_tac ring_is_ag)
 apply (frule aGroup.ag_carrier_carrier[THEN sym, of "R"])
 apply (frule aGroup.agop_gop [THEN sym, of "R"])
 apply (frule aGroup.agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubGroup_def)
apply (simp add:rcs_def)
done

lemma (in Ring) ar_coset_mem2:"\<lbrakk>ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^bsub>R\<^esub> I\<rbrakk> \<Longrightarrow>
                           \<exists>h\<in>I. x = a \<plusminus> h"
apply (cut_tac ring_is_ag)
apply (frule mem_ar_coset1 [of "I" "a" "x"], assumption+)
apply (erule bexE,
       frule_tac h = h in ideal_subset[of "I"], assumption+)
apply (simp add:aGroup.ag_pOp_commute[of "R" _ "a"],
       frule sym, thin_tac "a \<plusminus> h = x", blast)
done

lemma (in Ring) belong_ar_coset2:"\<lbrakk>ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^bsub>R\<^esub> I \<rbrakk>
                                    \<Longrightarrow> x \<plusminus> (-\<^sub>a a) \<in> I"
apply (cut_tac ring_is_ag)
apply (frule mem_ar_coset1, assumption+, erule bexE)
 apply (frule sym, thin_tac "h \<plusminus> a = x", simp)
 apply (frule_tac h = h in ideal_subset[of "I"], assumption)
 apply (frule aGroup.ag_mOp_closed[of "R" "a"], assumption)
 apply (subst aGroup.ag_pOp_assoc, assumption+,
        simp add:aGroup.ag_r_inv1,
        simp add:aGroup.ag_r_zero)
done

lemma (in Ring) ar_c_top: "\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R\<rbrakk>
       \<Longrightarrow> (c_top (b_ag R) I (a \<uplus>\<^bsub>R\<^esub> I) (b \<uplus>\<^bsub>R\<^esub> I)) = (a \<plusminus> b) \<uplus>\<^bsub>R\<^esub> I"
apply (cut_tac ring_is_ag, frule ideal_asubg,
       frule aGroup.asubg_nsubg[of "R" "I"], assumption,
       frule aGroup.b_ag_group[of "R"])
apply (simp add:ar_coset_def)
apply (subst Group.c_top_welldef[THEN sym], assumption+)
apply (simp add:aGroup.ag_carrier_carrier)+
apply (simp add:aGroup.agop_gop)
done

text\<open>Following lemma is not necessary to define a quotient ring. But
it makes clear that the binary operation2 of the quotient ring is well
defined.\<close>

lemma (in Ring) quotient_ring_tr1:"\<lbrakk>ideal R I; a1 \<in> carrier R; a2 \<in> carrier R;
                b1 \<in> carrier R; b2 \<in> carrier R;
                a1 \<uplus>\<^bsub>R\<^esub> I = a2 \<uplus>\<^bsub>R\<^esub> I; b1 \<uplus>\<^bsub>R\<^esub> I = b2 \<uplus>\<^bsub>R\<^esub> I\<rbrakk> \<Longrightarrow>
                             (a1 \<cdot>\<^sub>r b1) \<uplus>\<^bsub>R\<^esub> I = (a2 \<cdot>\<^sub>r b2) \<uplus>\<^bsub>R\<^esub> I"
apply (rule ar_coset_same1, assumption+)
 apply (simp add: ring_tOp_closed)+
apply (frule ar_coset_same2 [of "I" "a1" "a2"], assumption+)
apply (frule ar_coset_same2 [of "I" "b1" "b2"], assumption+)
apply (frule ring_distrib4[of "a2" "b2" "a1" "b1"], assumption+)
 apply simp
 apply (rule ideal_pOp_closed[of "I"], assumption)
 apply (simp add:ideal_ring_multiple, simp add:ideal_ring_multiple1)
done

definition
  rcostOp :: "[_, 'a set] \<Rightarrow> (['a set, 'a set] \<Rightarrow> 'a set)" where
  "rcostOp R I = (\<lambda>X\<in>(set_rcs (b_ag R) I). \<lambda>Y\<in>(set_rcs (b_ag R) I).
                {z. \<exists> x \<in> X. \<exists> y \<in> Y. \<exists>h\<in>I. (x \<cdot>\<^sub>r\<^bsub>R\<^esub> y) \<plusminus>\<^bsub>R\<^esub> h = z})"

lemma (in Ring) rcostOp:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
                    rcostOp R I (a \<uplus>\<^bsub>R\<^esub> I) (b \<uplus>\<^bsub>R\<^esub> I) = (a \<cdot>\<^sub>r b) \<uplus>\<^bsub>R\<^esub> I"
apply (cut_tac ring_is_ag)
 apply (frule ar_cos_mem[of "I" "a"], assumption+)
 apply (frule ar_cos_mem[of "I" "b"], assumption+)
apply (simp add:rcostOp_def)
apply (rule equalityI)
 apply (rule subsetI, simp) apply (erule bexE)+
 apply (rule belong_ar_coset1, assumption+)
 apply (simp add:ring_tOp_closed)
 apply (frule sym, thin_tac "xa \<cdot>\<^sub>r y \<plusminus> h = x", simp)
 apply (rule aGroup.ag_pOp_closed, assumption)
 apply (frule_tac x = xa in ar_coset_mem2[of "I" "a"], assumption+,
        frule_tac x = y in ar_coset_mem2[of "I" "b"], assumption+,
        (erule bexE)+, simp)
 apply (rule ring_tOp_closed, rule aGroup.ag_pOp_closed, assumption+,
        simp add:ideal_subset)
 apply (rule aGroup.ag_pOp_closed, assumption+, simp add:ideal_subset,
        simp add:ideal_subset)
 apply (frule sym, thin_tac "xa \<cdot>\<^sub>r y \<plusminus> h = x", simp)
 apply (frule_tac x = xa in belong_ar_coset2[of "I" "a"], assumption+,
        frule_tac x = y in belong_ar_coset2[of "I" "b"], assumption+)
 apply (frule_tac x = xa in ar_coset_subsetD[of "I" "a"], assumption+,
        frule_tac x = y in ar_coset_subsetD[of "I" "b"], assumption+)
 apply (subst aGroup.ag_pOp_commute, assumption,
        simp add:ring_tOp_closed, simp add:ideal_subset)
 apply (subst aGroup.ag_pOp_assoc, assumption,
        simp add:ideal_subset, simp add:ring_tOp_closed,
        rule aGroup.ag_mOp_closed, simp add:ring_tOp_closed,
        simp add:ring_tOp_closed)
 apply (rule ideal_pOp_closed, assumption+)
 apply (rule_tac a = xa and a' = y and b = a and b' = b in times_modTr,
        assumption+)

 apply (rule subsetI, simp)
 apply (frule_tac x = x in ar_coset_mem2[of "I" "a \<cdot>\<^sub>r b"],
        simp add:ring_tOp_closed, assumption)
 apply (erule bexE) apply simp
 apply (frule a_in_ar_coset[of "I" "a"], assumption+,
        frule a_in_ar_coset[of "I" "b"], assumption+)
 apply blast
done

definition
  qring ::  "[('a, 'm) Ring_scheme, 'a set] \<Rightarrow> \<lparr> carrier :: 'a set set,
    pop :: ['a  set, 'a set] \<Rightarrow> 'a set, mop :: 'a set \<Rightarrow> 'a set,
    zero :: 'a set, tp :: ['a  set, 'a set] \<Rightarrow> 'a set, un :: 'a set \<rparr>" where
  "qring R I = \<lparr> carrier = set_rcs (b_ag R) I,
    pop = c_top (b_ag R) I,
    mop = c_iop (b_ag R) I,
    zero = I,
    tp = rcostOp R I,
    un = 1\<^sub>r\<^bsub>R\<^esub> \<uplus>\<^bsub>R\<^esub> I\<rparr>"

abbreviation
  QRING  (infixl "'/\<^sub>r" 200) where
  "R /\<^sub>r I == qring R I"

lemma (in Ring) carrier_qring:"ideal R I \<Longrightarrow>
                               carrier (qring R I) = set_rcs (b_ag R) I"
by (simp add:qring_def)

lemma (in Ring) carrier_qring1:"ideal R I \<Longrightarrow>
                                carrier (qring R I) = set_ar_cos R I"
apply (cut_tac ring_is_ag)
apply (simp add:carrier_qring set_rcs_def set_ar_cos_def)
apply (simp add:ar_coset_def aGroup.ag_carrier_carrier)
done

lemma (in Ring) qring_ring:"ideal R I \<Longrightarrow> Ring (qring R I)"
apply (cut_tac ring_is_ag)
apply (frule ideal_asubg[of "I"],
        frule aGroup.asubg_nsubg[of "R" "I"], assumption,
        frule aGroup.b_ag_group[of "R"])
apply (subst Ring_def, simp)
apply (rule conjI)
 apply (rule Pi_I)+
 apply (simp add:carrier_qring, simp add:set_rcs_def, (erule bexE)+)
 apply (subst qring_def, simp)
 apply (subst Group.c_top_welldef[THEN sym, of "b_ag R" "I"], assumption+)
 apply (blast dest: Group.mult_closed[of "b_ag R"])
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:qring_def)
 apply (simp add:Group.Qg_tassoc[of "b_ag R" "I"])
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:qring_def)
 apply (simp add:set_rcs_def, (erule bexE)+, simp)
 apply (subst Group.c_top_welldef[THEN sym, of "b_ag R" "I"], assumption+)+
 apply (simp add:aGroup.agop_gop)
 apply (simp add:aGroup.ag_carrier_carrier)
 apply (simp add:aGroup.ag_pOp_commute)
apply (rule conjI)
 apply (simp add:qring_def Group.Qg_iop_closed)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (simp add:qring_def)
 apply (simp add:Group.Qg_i[of "b_ag R" "I"])
apply (rule conjI)
 apply (simp add:qring_def)
 apply (frule Group.nsg_sg[of "b_ag R" "I"], assumption)
 apply (simp add:Group.unit_rcs_in_set_rcs)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (simp add:qring_def)
 apply (simp add:Group.Qg_unit[of "b_ag R" "I"])
apply (rule conjI)
apply(rule Pi_I)+
 apply (simp add:qring_def aGroup.aqgrp_carrier)
 apply (simp add:set_ar_cos_def, (erule bexE)+, simp add:rcostOp,
        blast dest: ring_tOp_closed)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:qring_def aGroup.aqgrp_carrier)
 apply (simp add:set_ar_cos_def, (erule bexE)+, simp add:rcostOp)
 apply (frule_tac x = aa and y = ab in ring_tOp_closed, assumption+,
        frule_tac x = ab and y = ac in ring_tOp_closed, assumption+,
        simp add:rcostOp, simp add:ring_tOp_assoc)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:qring_def aGroup.aqgrp_carrier)
 apply (simp add:set_ar_cos_def, (erule bexE)+, simp add:rcostOp,
        simp add:ring_tOp_commute)
apply (rule conjI)
 apply (simp add:qring_def aGroup.aqgrp_carrier)
 apply (cut_tac ring_one, simp add:set_ar_cos_def, blast)
apply (rule conjI)
 apply (rule allI, rule impI)+
 apply (simp add:qring_def aGroup.aqgrp_carrier)
 apply (simp add:set_ar_cos_def, (erule bexE)+, simp)
 apply (simp add:ar_c_top rcostOp)
 apply (frule_tac x = ab and y = ac in aGroup.ag_pOp_closed,
                  assumption+,
        frule_tac x = aa and y = ab in ring_tOp_closed, assumption+ ,
        frule_tac x = aa and y = ac in ring_tOp_closed, assumption+)
 apply (simp add:ar_c_top rcostOp, simp add:ring_distrib1)
apply (rule allI, rule impI)
  apply (simp add:qring_def aGroup.aqgrp_carrier)
  apply (simp add:set_ar_cos_def, erule bexE, simp)
  apply (cut_tac ring_one)
  apply (simp add:rcostOp, simp add:ring_l_one)
done

lemma (in Ring) qring_carrier:"ideal R I \<Longrightarrow>
              carrier (qring R I)  = {X. \<exists>a\<in> carrier R. a \<uplus>\<^bsub>R\<^esub> I = X}"
apply (simp add:carrier_qring1 set_ar_cos_def)
apply (rule equalityI)
 apply (rule subsetI, simp, erule bexE, frule sym, thin_tac "x = a \<uplus>\<^bsub>R\<^esub> I",
        blast)
apply (rule subsetI, simp, erule bexE, frule sym, thin_tac "a \<uplus>\<^bsub>R\<^esub> I = x",
       blast)
done

lemma (in Ring) qring_mem:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                                 a \<uplus>\<^bsub>R\<^esub> I \<in> carrier (qring R I)"
apply (simp add:qring_carrier)
apply blast
done

lemma (in Ring) qring_pOp:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R \<rbrakk>
 \<Longrightarrow> pop (qring R I) (a \<uplus>\<^bsub>R\<^esub> I) (b \<uplus>\<^bsub>R\<^esub> I) = (a \<plusminus> b) \<uplus>\<^bsub>R\<^esub> I"
by (simp add:qring_def, simp add:ar_c_top)

lemma (in Ring) qring_zero:"ideal R I \<Longrightarrow> zero (qring R I) = I"
apply (simp add:qring_def)
done

lemma (in Ring) qring_zero_1:"\<lbrakk>a \<in> carrier R; ideal R I; a \<uplus>\<^bsub>R\<^esub> I = I\<rbrakk> \<Longrightarrow>
                                    a \<in> I"
by (frule a_in_ar_coset [of "I" "a"], assumption+, simp)

lemma (in Ring) Qring_fix1:"\<lbrakk>a \<in> carrier R; ideal R I; a \<in> I\<rbrakk> \<Longrightarrow> a \<uplus>\<^bsub>R\<^esub> I = I"
apply (cut_tac ring_is_ag, frule aGroup.b_ag_group)
apply (simp add:ar_coset_def)
apply (frule ideal_asubg[of "I"], simp add:asubGroup_def)
apply (simp add:Group.rcs_fixed2[of "b_ag R" "I"])
done

lemma (in Ring) ar_cos_same:"\<lbrakk>a \<in> carrier R; ideal R I; x \<in> a \<uplus>\<^bsub>R\<^esub> I\<rbrakk> \<Longrightarrow>
                                x \<uplus>\<^bsub>R\<^esub> I = a \<uplus>\<^bsub>R\<^esub> I"
apply (cut_tac ring_is_ag)
apply (rule ar_coset_same1[of "I" "x" "a"], assumption+)
apply (rule ar_coset_subsetD[of "I"], assumption+)
apply (frule ar_coset_mem2[of "I" "a" "x"], assumption+,
       erule bexE)
apply (frule_tac h = h in ideal_subset[of "I"], assumption,
      simp add:aGroup.ag_p_inv)
apply (frule_tac x = a in aGroup.ag_mOp_closed[of "R"], assumption+,
       frule_tac x = h in aGroup.ag_mOp_closed[of "R"], assumption+)
apply (simp add:aGroup.ag_pOp_assoc[THEN sym],
       simp add:aGroup.ag_r_inv1 aGroup.ag_l_zero)
apply (simp add:ideal_inv1_closed)
done

lemma (in Ring) qring_tOp:"\<lbrakk>ideal R I; a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
                tp (qring R I) (a \<uplus>\<^bsub>R\<^esub> I) (b \<uplus>\<^bsub>R\<^esub> I) = (a \<cdot>\<^sub>r b) \<uplus>\<^bsub>R\<^esub> I"
by (simp add:qring_def, simp add:rcostOp)

lemma rind_hom_well_def:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R; a \<in> carrier A \<rbrakk> \<Longrightarrow>
                                   f a = (f\<degree>\<^bsub>A,R\<^esub>) (a \<uplus>\<^bsub>A\<^esub> (ker\<^bsub>A,R\<^esub> f))"
apply (frule ker_ideal[of "A" "R" "f"], assumption+)
apply (frule Ring.mem_set_ar_cos[of "A" "ker\<^bsub>A,R\<^esub> f" "a"], assumption+)
apply (simp add:rind_hom_def)
 apply (rule someI2_ex)
 apply (frule Ring.a_in_ar_coset [of "A" "ker\<^bsub>A,R\<^esub> f" "a"], assumption+, blast)
 apply (frule_tac x = x in Ring.ar_coset_mem2[of "A" "ker\<^bsub>A,R\<^esub> f" "a"],
           assumption+, erule bexE, simp,
        frule_tac h = h in Ring.ideal_subset[of "A" "ker\<^bsub>A,R\<^esub> f"], assumption+)
 apply (frule_tac Ring.ring_is_ag[of "A"],
        frule_tac Ring.ring_is_ag[of "R"],
        simp add:rHom_def, frule conjunct1, simp add:aHom_add)
 apply (simp add:ker_def)
 apply (frule aHom_mem[of "A" "R" "f" "a"], assumption+,
        simp add:aGroup.ag_r_zero)
done

lemma (in Ring) set_r_ar_cos:"ideal R I \<Longrightarrow>
                 set_rcs (b_ag R) I = set_ar_cos R I"
 apply (simp add:set_ar_cos_def set_rcs_def ar_coset_def)
 apply (cut_tac ring_is_ag)
 apply (simp add:aGroup.ag_carrier_carrier)
done

lemma set_r_ar_cos_ker:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow>
                     set_rcs (b_ag A) (ker\<^bsub>A,R\<^esub> f) = set_ar_cos A (ker\<^bsub>A,R\<^esub> f)"
apply (frule ker_ideal[of "A" "R" "f"], assumption+)
 apply (simp add:Ring.carrier_qring[THEN sym],
        simp add:Ring.carrier_qring1[THEN sym])
done

lemma ind_hom_rhom:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                                    (f\<degree>\<^bsub>A,R\<^esub>) \<in> rHom (qring A (ker\<^bsub>A,R\<^esub> f)) R"
apply (simp add:rHom_def [of "qring A (ker\<^bsub>A,R\<^esub> f)" "R"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:qring_def)
apply (simp add:rind_hom_def extensional_def)
apply (rule Pi_I)
 apply (frule Ring.ring_is_ag [of "A"], frule Ring.ring_is_ag [of "R"],
        frule aGroup.b_ag_group [of "R"])
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:set_ar_cos_def)
 apply (rule conjI)
 apply (rule impI)
 apply (erule bexE, simp)
 apply (frule ker_ideal [of "A" "R" "f"], assumption+)
 apply (frule_tac a = a in Ring.a_in_ar_coset [of "A" "ker\<^bsub>A,R\<^esub> f"],
        assumption+)
 apply (rule someI2_ex, blast)
 apply (frule_tac I = "ker\<^bsub>A,R\<^esub> f" and a = a and x = xa in
                   Ring.ar_coset_subsetD[of "A"], assumption+)
 apply (simp add:aGroup.ag_carrier_carrier, simp add:rHom_mem)
 apply (simp add:set_r_ar_cos_ker, simp add:set_ar_cos_def, rule impI, blast)
apply (rule conjI)
 apply (simp add:qring_def)
 apply (simp add:set_r_ar_cos_ker)
 apply (simp add:rind_hom_def extensional_def)
apply (rule ballI)+
 apply (simp add:qring_def)
 apply (simp add:set_r_ar_cos_ker)
 apply (simp add:set_ar_cos_def)
 apply ((erule bexE)+, simp)
 apply (frule ker_ideal[of "A" "R" "f"], assumption+)
 apply (simp add:Ring.ar_c_top)
 apply (frule Ring.ring_is_ag[of "A"],
        frule Ring.ring_is_ag[of "R"],
        frule_tac x = aa and y = ab in aGroup.ag_pOp_closed[of "A"],
        assumption+)
 apply (simp add:rind_hom_well_def[THEN sym])
 apply (simp add:rHom_def, frule conjunct1, simp add:aHom_add)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule ker_ideal[of "A" "R" "f"], assumption+,
        simp add:Ring.carrier_qring1, simp add:set_ar_cos_def,
        (erule bexE)+, simp add:qring_def Ring.rcostOp)
 apply (frule Ring.ring_is_ag[of "A"],
         frule_tac x = a and y = aa in Ring.ring_tOp_closed[of "A"],
         assumption+)
 apply (simp add:rind_hom_well_def[THEN sym], simp add:rHom_tOp)

apply (simp add:qring_def)
 apply (frule Ring.ring_one[of "A"],
        simp add:rind_hom_well_def[THEN sym],
        simp add:rHom_one)
done

lemma ind_hom_injec:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                              injec\<^bsub>(qring A (ker\<^bsub>A,R\<^esub> f)),R\<^esub> (f\<degree>\<^bsub>A,R\<^esub>)"
apply (simp add:injec_def)
apply (frule ind_hom_rhom [of "A" "R" "f"], assumption+)
apply (frule rHom_aHom[of "f\<degree>\<^bsub>A,R\<^esub>" "A /\<^sub>r (ker\<^bsub>A,R\<^esub> f)" "R"], simp)
 apply (simp add:ker_def[of _ _ "f\<degree>\<^bsub>A,R\<^esub>"])
apply ((subst qring_def)+, simp)
 apply (simp add:set_r_ar_cos_ker)

apply (frule Ring.ring_is_ag[of "A"],
       frule Ring.ring_is_ag[of "R"],
       frule ker_ideal[of "A" "R" "f"], assumption+)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp, erule conjE)
 apply (simp add:set_ar_cos_def, erule bexE, simp)
 apply (simp add:rind_hom_well_def[THEN sym, of "A" "R" "f"],
        thin_tac "x = a \<uplus>\<^bsub>A\<^esub> ker\<^bsub>A,R\<^esub> f")
 apply (rule_tac a = a in Ring.Qring_fix1[of "A" _ "ker\<^bsub>A,R\<^esub> f"], assumption+)
 apply (simp add:ker_def)

 apply (rule subsetI, simp)
 apply (simp add:Ring.I_in_set_ar_cos[of "A" "ker\<^bsub>A,R\<^esub> f"])
 apply (frule Ring.ideal_zero[of "A" "ker\<^bsub>A,R\<^esub> f"], assumption+,
        frule Ring.ring_zero[of "A"])

 apply (frule Ring.ar_coset_same4[of "A" "ker\<^bsub>A,R\<^esub> f" "\<zero>\<^bsub>A\<^esub>"], assumption+)
 apply (frule rind_hom_well_def[THEN sym, of "A" "R" "f" "\<zero>\<^bsub>A\<^esub>"], assumption+)
 apply simp

 apply (rule rHom_0_0, assumption+)
done

lemma rhom_to_rimg:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                                   f \<in> rHom A (rimg A R f)"
apply (frule Ring.ring_is_ag[of "A"], frule Ring.ring_is_ag[of "R"])
apply (subst rHom_def, simp)
apply (rule conjI)
 apply (subst aHom_def, simp)
 apply (rule conjI)
 apply (simp add:rimg_def)
 apply (rule conjI)
  apply (simp add:rHom_def aHom_def)
  apply ((rule ballI)+, simp add:rimg_def)
 apply (rule aHom_add, assumption+)
  apply (simp add:rHom_aHom, assumption+)

 apply (rule conjI)
 apply ((rule ballI)+, simp add:rimg_def, simp add:rHom_tOp)

 apply (simp add:rimg_def, simp add:rHom_one)
done

lemma ker_to_rimg:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow>
                         ker\<^bsub>A,R\<^esub> f = ker\<^bsub>A,(rimg A R f)\<^esub> f"
apply (frule rhom_to_rimg [of "A" "R" "f"], assumption+)
apply (simp add:ker_def)
apply (simp add:rimg_def)
done

lemma indhom_eq:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow> f\<degree>\<^bsub>A,(rimg A R f)\<^esub> = f\<degree>\<^bsub>A,R\<^esub>"
apply (frule rimg_ring[of "A" "R" "f"], assumption+)
apply (frule rhom_to_rimg[of "A" "R" "f"], assumption+,
       frule ind_hom_rhom[of "A" "rimg A R f"], assumption+,
       frule ind_hom_rhom[of "A" "R" "f"], assumption+) (** extensional **)
apply (rule funcset_eq[of "f\<degree>\<^bsub>A,rimg A R f\<^esub> " "carrier (A /\<^sub>r (ker\<^bsub>A,R\<^esub> f))" "f\<degree>\<^bsub>A,R\<^esub>"])
 apply (simp add:ker_to_rimg[THEN sym],
        simp add:rHom_def[of _ "rimg A R f"] aHom_def)
 apply (simp add:rHom_def[of _ "R"] aHom_def)

apply (simp add:ker_to_rimg[THEN sym])
 apply (rule ballI)
 apply (frule ker_ideal[of "A" "R" "f"], assumption+,
        simp add:Ring.carrier_qring1)
 apply (simp add:set_ar_cos_def, erule bexE, simp)
 apply (simp add:rind_hom_well_def[THEN sym])
 apply (frule rind_hom_well_def[THEN sym, of "A" "rimg A R f" "f"],
         assumption+, simp add:ker_to_rimg[THEN sym])
done

lemma indhom_bijec2_rimg:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                    bijec\<^bsub>(qring A (ker\<^bsub>A,R\<^esub> f)),(rimg A R f)\<^esub> (f\<degree>\<^bsub>A,R\<^esub>)"
apply (frule rimg_ring [of "A" "R" "f"], assumption+)
apply (frule rhom_to_rimg[of "A" "R" "f"], assumption+)
apply (frule ind_hom_rhom[of "A" "rimg A R f" "f"], assumption+)
 apply (frule ker_to_rimg[THEN sym, of "A" "R" "f"], assumption+)
 apply (frule indhom_eq[of "A" "R" "f"], assumption+)
apply simp
 apply (simp add:bijec_def)
 apply (rule conjI)
  apply (simp add:injec_def)
   apply (rule conjI)
   apply (simp add:rHom_def)
   apply (frule ind_hom_injec [of "A" "R" "f"], assumption+)
   apply (simp add:injec_def)
   apply (simp add:ker_def [of _ _ "f\<degree>\<^bsub>A,R\<^esub>"])
   apply (simp add:rimg_def)

  apply (simp add:surjec_def)
   apply (rule conjI)
   apply (simp add:rHom_def)
   apply (rule surj_to_test)
   apply (simp add:rHom_def aHom_def)
   apply (rule ballI)
   apply (simp add:rimg_carrier)
   apply (simp add:image_def)
   apply (erule bexE, simp)
   apply (frule_tac a1 = x in rind_hom_well_def[THEN sym, of "A" "R" "f"],
                   assumption+)
   apply (frule ker_ideal[of "A" "R" "f"], assumption+,
        simp add:Ring.carrier_qring1,
        frule_tac a = x in Ring.mem_set_ar_cos[of "A" "ker\<^bsub>A,R\<^esub> f"], assumption+)
 apply blast
done

lemma surjec_ind_bijec:"\<lbrakk>Ring A; Ring R; f \<in> rHom A R; surjec\<^bsub>A,R\<^esub> f\<rbrakk> \<Longrightarrow>
     bijec\<^bsub>(qring A (ker\<^bsub>A,R\<^esub> f)),R\<^esub> (f\<degree>\<^bsub>A,R\<^esub>)"
apply (frule ind_hom_rhom[of "A" "R" "f"], assumption+)
apply (simp add:surjec_def)
apply (simp add:bijec_def)
 apply (simp add:ind_hom_injec)

 apply (simp add:surjec_def)
   apply (simp add:rHom_aHom)
   apply (rule surj_to_test)
   apply (simp add:rHom_def aHom_def)
   apply (rule ballI)
   apply (simp add:surj_to_def, frule sym,
                        thin_tac "f ` carrier A = carrier R", simp,
                        thin_tac "carrier R = f ` carrier A")
   apply (simp add:image_def, erule bexE)
   apply (frule_tac a1 = x in rind_hom_well_def[THEN sym, of "A" "R" "f"],
                   assumption+)
   apply (frule ker_ideal[of "A" "R" "f"], assumption+,
        simp add:Ring.carrier_qring1,
        frule_tac a = x in Ring.mem_set_ar_cos[of "A" "ker\<^bsub>A,R\<^esub> f"], assumption+)
 apply blast
done

lemma ridmap_ind_bijec:"Ring A \<Longrightarrow>
     bijec\<^bsub>(qring A (ker\<^bsub>A,A\<^esub> (ridmap A))),A\<^esub> ((ridmap A)\<degree>\<^bsub>A,A\<^esub>)"
apply (frule ridmap_surjec[of "A"])
apply (rule surjec_ind_bijec [of "A" "A" "ridmap A"], assumption+)
 apply (simp add:rHom_def, simp add:surjec_def)

 apply (rule conjI)
  apply (rule ballI)+
  apply (frule_tac x = x and y = y in Ring.ring_tOp_closed[of "A"],
          assumption+, simp add:ridmap_def)
  apply (simp add:ridmap_def Ring.ring_one)

 apply assumption
done

lemma ker_of_idmap:"Ring A \<Longrightarrow> ker\<^bsub>A,A\<^esub> (ridmap A) = {\<zero>\<^bsub>A\<^esub>}"
apply (simp add:ker_def)
apply (simp add:ridmap_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (rule subsetI) apply (simp add:CollectI)

 apply (simp add:Ring.ring_zero)
done

lemma ring_natural_isom:"Ring A \<Longrightarrow>
         bijec\<^bsub>(qring A {\<zero>\<^bsub>A\<^esub>}),A\<^esub> ((ridmap A)\<degree>\<^bsub>A,A\<^esub>)"
apply (frule ridmap_ind_bijec)
apply (simp add: ker_of_idmap)
done           (** A /\<^sub>r {0\<^sub>A}\<^sub> \<cong> A **)

definition
  pj :: "[('a, 'm) Ring_scheme, 'a set] \<Rightarrow> ('a => 'a set)" where
  "pj R I = (\<lambda>x. Pj (b_ag R) I x)"

 (* pj is projection homomorphism *)

lemma pj_Hom:"\<lbrakk>Ring R; ideal R I\<rbrakk> \<Longrightarrow> (pj R I) \<in> rHom R (qring R I)"
apply (simp add:rHom_def)
apply (rule conjI)
apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:qring_def)
 apply (frule Ring.ring_is_ag)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:set_rcs_def) apply blast
apply (rule conjI)
 apply (simp add:pj_def Pj_def extensional_def)
 apply (frule Ring.ring_is_ag) apply (simp add:aGroup.ag_carrier_carrier)
apply (rule ballI)+
 apply (frule Ring.ring_is_ag)
 apply (frule_tac x = a and y = b in aGroup.ag_pOp_closed, assumption+)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:qring_def) apply (frule aGroup.b_ag_group)
 apply (simp add:aGroup.agop_gop [THEN sym])
 apply (subst Group.c_top_welldef[of "b_ag R" "I"], assumption+)
 apply (frule Ring.ideal_asubg[of "R" "I"], assumption+)
 apply (simp add:aGroup.asubg_nsubg)
 apply assumption+
 apply simp

apply (rule conjI)
 apply (rule ballI)+
 apply (simp add: qring_def)
 apply (frule_tac x = x and y = y in Ring.ring_tOp_closed, assumption+)
 apply (frule Ring.ring_is_ag)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:aGroup.ag_carrier_carrier)

 apply (frule_tac a1 = x and b1 = y in Ring.rcostOp [THEN sym, of "R" "I"],
                                                             assumption+)
 apply (simp add:ar_coset_def)
apply (simp add:qring_def)
 apply (frule Ring.ring_one)
 apply (frule Ring.ring_is_ag)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:ar_coset_def)
done

lemma pj_mem:"\<lbrakk>Ring R; ideal R I; x \<in> carrier R\<rbrakk> \<Longrightarrow> pj R I x = x \<uplus>\<^bsub>R\<^esub> I"
apply (frule Ring.ring_is_ag)
apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
apply (simp add:pj_def Pj_def)
apply (simp add:ar_coset_def)
done

lemma pj_zero:"\<lbrakk>Ring R; ideal R I; x \<in> carrier R\<rbrakk> \<Longrightarrow>
                         (pj R I x = \<zero>\<^bsub>(R /\<^sub>r I)\<^esub>) = (x \<in> I)"
apply (rule iffI)
apply (simp add:pj_mem Ring.qring_zero,
       simp add:Ring.qring_zero_1[of "R" "x" "I"])
apply (simp add:pj_mem Ring.qring_zero,
       rule Ring.Qring_fix1, assumption+)
done

lemma pj_surj_to:"\<lbrakk>Ring R; ideal R J; X \<in> carrier (R /\<^sub>r J)\<rbrakk> \<Longrightarrow>
                   \<exists>r\<in> carrier R. pj R J r = X"
apply (simp add:qring_def set_rcs_def,
       fold ar_coset_def, simp add:b_ag_def, erule bexE,
       frule_tac x = a in pj_mem[of R J], assumption+, simp)
 apply blast
done

lemma invim_of_ideal:"\<lbrakk>Ring R; ideal R I; ideal (qring R I) J \<rbrakk> \<Longrightarrow>
  ideal R (rInvim R (qring R I) (pj R I) J)"
apply (rule Ring.ideal_condition, assumption)
 apply (simp add:rInvim_def) 
apply (subgoal_tac "\<zero>\<^bsub>R\<^esub> \<in> rInvim R (qring R I) (pj R I) J")
apply (simp add:nonempty)
apply (simp add:rInvim_def)
apply (simp add: Ring.ring_zero)
 apply (frule Ring.ring_is_ag)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (frule Ring.qring_ring [of "R" "I"], assumption+)
 apply (frule rHom_0_0 [of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:Ring.ideal_zero)
apply (rule ballI)+
 apply (simp add:rInvim_def) apply (erule conjE)+
 apply (rule conjI)
 apply (frule Ring.ring_is_ag)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (frule Ring.ring_is_ag)
 apply (frule_tac x = y in aGroup.ag_mOp_closed [of "R"], assumption+)
 apply (simp add:rHom_def) apply (erule conjE)+
 apply (subst aHom_add [of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:Ring.qring_ring Ring.ring_is_ag)
 apply assumption+
apply (frule Ring.qring_ring [of "R" "I"], assumption+)
 apply (rule Ring.ideal_pOp_closed, assumption+)
 apply (subst aHom_inv_inv[of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:Ring.ring_is_ag) apply assumption+
 apply (frule_tac x = "pj R I y" in Ring.ideal_inv1_closed [of "R /\<^sub>r I" "J"],
                                              assumption+)
apply (rule ballI)+
 apply (simp add:rInvim_def) apply (erule conjE)
 apply (simp add:Ring.ring_tOp_closed)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (subst rHom_tOp [of "R" "R /\<^sub>r I" _ _ "pj R I"], assumption+)
 apply (frule Ring.qring_ring[of "R" "I"], assumption+)
 apply (rule Ring.ideal_ring_multiple [of "R /\<^sub>r I" "J"])
 apply (simp add:Ring.qring_ring) apply assumption+
 apply (simp add:rHom_mem)
done

lemma pj_invim_cont_I:"\<lbrakk>Ring R; ideal R I; ideal (qring R I) J\<rbrakk> \<Longrightarrow>
                         I \<subseteq> (rInvim R (qring R I) (pj R I) J)"
apply (rule subsetI)
 apply (simp add:rInvim_def)
 apply (frule Ring.ideal_subset [of "R" "I"], assumption+)
 apply simp
 apply (frule  pj_mem [of "R" "I"  _], assumption+)
 apply (simp add:Ring.ar_coset_same4)
apply (frule  Ring.qring_ring[of "R" "I"], assumption+)
apply (frule Ring.ideal_zero [of "qring R I" "J"], assumption+)

apply (frule Ring.qring_zero[of "R" "I"], assumption)
 apply simp
done

lemma pj_invim_mono1:"\<lbrakk>Ring R; ideal R I; ideal (qring R I) J1;
      ideal (qring R I) J2; J1 \<subseteq> J2 \<rbrakk> \<Longrightarrow>
      (rInvim R (qring R I) (pj R I) J1) \<subseteq> (rInvim R (qring R I) (pj R I) J2)"
apply (rule subsetI)
apply (simp add:rInvim_def)
apply (simp add:subsetD)
done

lemma pj_img_ideal:"\<lbrakk>Ring R; ideal R I; ideal R J; I \<subseteq> J\<rbrakk> \<Longrightarrow>
                                  ideal (qring R I) ((pj R I)`J)"
apply (rule Ring.ideal_condition [of "qring R I" "(pj R I) `J"])
apply (simp add:Ring.qring_ring)
apply (rule subsetI, simp add:image_def)
 apply (erule bexE)
 apply (frule_tac h = xa in Ring.ideal_subset [of "R" "J"], assumption+)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (simp add:rHom_mem)
 apply (frule Ring.ideal_zero [of "R" "J"], assumption+)
 apply (simp add:image_def) apply blast
apply (rule ballI)+
 apply (simp add:image_def)
 apply (erule bexE)+
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (rename_tac x y s t)
 apply (frule_tac h = s in Ring.ideal_subset [of "R" "J"], assumption+)
 apply (frule_tac h = t in Ring.ideal_subset [of "R" "J"], assumption+)
 apply (simp add:rHom_def)   apply (erule conjE)+
 apply (frule Ring.ring_is_ag)
 apply (frule Ring.qring_ring [of "R" "I"], assumption+)
 apply (frule Ring.ring_is_ag [of "R /\<^sub>r I"])
  apply (frule_tac x = t in aGroup.ag_mOp_closed [of "R"], assumption+)
 apply (frule_tac a1 = s and b1 = "-\<^sub>a\<^bsub>R\<^esub> t" in aHom_add [of "R" "R /\<^sub>r I"
  "pj R I", THEN sym], assumption+) apply (simp add:aHom_inv_inv)
 apply (frule_tac x = t in Ring.ideal_inv1_closed [of "R" "J"], assumption+)
 apply (frule_tac x = s and y = "-\<^sub>a\<^bsub>R\<^esub> t" in Ring.ideal_pOp_closed [of "R" "J"],
                                             assumption+)
 apply blast
apply (rule ballI)+
apply (simp add:qring_def)
 apply (simp add:Ring.set_r_ar_cos)
 apply (simp add:set_ar_cos_def, erule bexE)
 apply simp
 apply (simp add:image_def)
 apply (erule bexE)
 apply (frule_tac x = xa in pj_mem [of "R" "I"], assumption+)
 apply (simp add:Ring.ideal_subset) apply simp
 apply (subst Ring.rcostOp, assumption+)
    apply (simp add:Ring.ideal_subset)
 apply (frule_tac x = xa and r = a in Ring.ideal_ring_multiple [of "R" "J"],
                                                  assumption+)
 apply (frule_tac h = "a \<cdot>\<^sub>r\<^bsub>R\<^esub> xa" in Ring.ideal_subset [of "R" "J"],
                                                                 assumption+)
 apply (frule_tac x1 = "a \<cdot>\<^sub>r\<^bsub>R\<^esub> xa" in pj_mem [THEN sym, of "R" "I"],
                                                                 assumption+)
 apply simp
 apply blast
done

lemma npQring:"\<lbrakk>Ring R; ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
      npow (qring R I) (a \<uplus>\<^bsub>R\<^esub> I) n = (npow R a n) \<uplus>\<^bsub>R\<^esub> I"
apply (induct_tac n)
apply (simp add:qring_def)

apply (simp add:qring_def)
apply (rule Ring.rcostOp, assumption+)
apply (rule Ring.npClose, assumption+)
done

section "Primary ideals, Prime ideals"

definition
  maximal_set :: "['a set set, 'a set] \<Rightarrow> bool" where
  "maximal_set S mx \<longleftrightarrow> mx \<in> S \<and> (\<forall>s\<in>S. mx \<subseteq> s \<longrightarrow> s = mx)"

definition
  nilpotent :: "[_, 'a] \<Rightarrow> bool" where
  "nilpotent R a \<longleftrightarrow> (\<exists>(n::nat). a^\<^bsup>R n\<^esup> = \<zero>\<^bsub>R\<^esub>)"

definition
 zero_divisor :: "[_, 'a] \<Rightarrow> bool" where
  "zero_divisor R a \<longleftrightarrow> (\<exists>x\<in> carrier R. x \<noteq> \<zero>\<^bsub>R\<^esub> \<and> x \<cdot>\<^sub>r\<^bsub>R\<^esub> a = \<zero>\<^bsub>R\<^esub>)"

definition
  primary_ideal :: "[_, 'a set] \<Rightarrow> bool" where
  "primary_ideal R q \<longleftrightarrow> ideal R q \<and> (1\<^sub>r\<^bsub>R\<^esub>) \<notin> q \<and>
    (\<forall>x\<in> carrier R. \<forall>y\<in> carrier R.
      x \<cdot>\<^sub>r\<^bsub>R\<^esub> y \<in> q  \<longrightarrow> (\<exists>n. (npow R x n) \<in> q \<or> y \<in> q))"

definition
  prime_ideal :: "[_, 'a set] \<Rightarrow> bool" where
  "prime_ideal R p \<longleftrightarrow> ideal R p \<and> (1\<^sub>r\<^bsub>R\<^esub>) \<notin> p \<and> (\<forall>x\<in> carrier R. \<forall>y\<in> carrier R.
    (x \<cdot>\<^sub>r\<^bsub>R\<^esub> y \<in> p \<longrightarrow> x \<in> p \<or> y \<in> p))"

definition
  maximal_ideal :: "[_, 'a set] \<Rightarrow> bool" where
  "maximal_ideal R mx \<longleftrightarrow> ideal R mx \<and> 1\<^sub>r\<^bsub>R\<^esub> \<notin> mx \<and>
        {J. (ideal R J \<and> mx \<subseteq> J)} = {mx, carrier R}"

lemma (in Ring) maximal_ideal_ideal:"\<lbrakk>maximal_ideal R mx\<rbrakk> \<Longrightarrow> ideal R mx"
by (simp add:maximal_ideal_def)

lemma (in Ring) maximal_ideal_proper:"maximal_ideal R mx \<Longrightarrow> 1\<^sub>r \<notin> mx"
by (simp add:maximal_ideal_def)

lemma (in Ring) prime_ideal_ideal:"prime_ideal R I \<Longrightarrow> ideal R I"
by (simp add:prime_ideal_def)

lemma (in Ring) prime_ideal_proper:"prime_ideal R I \<Longrightarrow> I \<noteq> carrier R"
apply (simp add:prime_ideal_def, (erule conjE)+)
apply (simp add:proper_ideal)
done

lemma (in Ring) prime_ideal_proper1:"prime_ideal R p \<Longrightarrow> 1\<^sub>r \<notin> p"
by (simp add:prime_ideal_def)

lemma (in Ring) primary_ideal_ideal:"primary_ideal R q \<Longrightarrow> ideal R q"
by (simp add:primary_ideal_def)

lemma (in Ring)  primary_ideal_proper1:"primary_ideal R q \<Longrightarrow> 1\<^sub>r \<notin> q"
by (simp add:primary_ideal_def)

lemma (in Ring) prime_elems_mult_not:"\<lbrakk>prime_ideal R P; x \<in> carrier R;
                y \<in> carrier R; x \<notin> P; y \<notin> P \<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>r y \<notin> P"
apply (simp add:prime_ideal_def, (erule conjE)+)
apply (rule contrapos_pp, simp+)
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P",
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P", simp)
done


lemma (in Ring) prime_is_primary:"prime_ideal R p \<Longrightarrow> primary_ideal R p"
apply (unfold primary_ideal_def)
apply (rule conjI, simp add:prime_ideal_def)
apply (rule conjI, simp add:prime_ideal_def)
apply ((rule ballI)+, rule impI)
apply (simp add:prime_ideal_def, (erule conjE)+)
 apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> p \<longrightarrow> x \<in> p \<or> y \<in> p",
        frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> p \<longrightarrow> x \<in> p \<or> y \<in> p", simp)
 apply (erule disjE)
 apply (frule_tac t = x in np_1[THEN sym])
 apply (frule_tac a = x and A = p and b = "x^\<^bsup>R (Suc 0)\<^esup>" in eq_elem_in,
                                               assumption)
 apply blast
apply simp
done

lemma (in Ring) maximal_prime_Tr0:"\<lbrakk>maximal_ideal R mx; x \<in> carrier R; x \<notin> mx\<rbrakk>
              \<Longrightarrow>  mx \<minusplus> (Rxa R x) = carrier R"
apply (frule principal_ideal [of "x"])
 apply (frule maximal_ideal_ideal[of "mx"])
 apply (frule sum_ideals [of "mx" "Rxa R x"], assumption)
 apply (frule sum_ideals_la1 [of "mx" "Rxa R x"], assumption)
 apply (simp add:maximal_ideal_def)
 apply (erule conjE)+
 apply (subgoal_tac "mx \<minusplus> (Rxa R x) \<in> {J. ideal R J \<and> mx \<subseteq> J}")
 apply simp
apply (frule sum_ideals_la2 [of "mx" "Rxa R x"], assumption+)
  apply (frule a_in_principal [of "x"])
  apply (frule subsetD [of "Rxa R x" "mx \<minusplus> (Rxa R x)" "x"], assumption+)
 apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
apply (erule disjE)
 apply simp apply simp

apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply simp
done

lemma (in Ring) maximal_prime:"maximal_ideal R mx \<Longrightarrow> prime_ideal R mx"
apply (cut_tac ring_is_ag)
apply (simp add:prime_ideal_def)
apply (simp add:maximal_ideal_ideal)
apply (simp add:maximal_ideal_proper)

apply ((rule ballI)+, rule impI)
apply (rule contrapos_pp, simp+, erule conjE)
apply (frule_tac x = x in maximal_prime_Tr0[of "mx"], assumption+,
       frule_tac x = y in maximal_prime_Tr0[of "mx"], assumption+,
       frule maximal_ideal_ideal[of mx],
       frule ideal_subset1[of mx],
       frule_tac a = x in principal_ideal,
       frule_tac a = y in principal_ideal,
       frule_tac I = "R \<diamondsuit>\<^sub>p x" in ideal_subset1,
       frule_tac I = "R \<diamondsuit>\<^sub>p y" in ideal_subset1)
apply (simp add:aGroup.set_sum)
 apply (cut_tac ring_one)
 apply (frule sym,
        thin_tac "{xa. \<exists>h\<in>mx. \<exists>k\<in>R \<diamondsuit>\<^sub>p x. xa = h \<plusminus> k} = carrier R",
        frule sym,
        thin_tac "{x. \<exists>h\<in>mx. \<exists>k\<in>R \<diamondsuit>\<^sub>p y. x = h \<plusminus> k} = carrier R")
 apply (frule_tac a = "1\<^sub>r" and B = "{xa. \<exists>i\<in>mx. \<exists>j\<in>(Rxa R x). xa = i \<plusminus> j}" in
                         eq_set_inc[of _ "carrier R"], assumption,
        frule_tac a = "1\<^sub>r" and B = "{xa. \<exists>i\<in>mx. \<exists>j\<in>(Rxa R y). xa = i \<plusminus> j}" in
                         eq_set_inc[of _ "carrier R"], assumption,
        thin_tac "carrier R = {xa. \<exists>i\<in>mx. \<exists>j\<in>(Rxa R x). xa = i \<plusminus> j}",
        thin_tac "carrier R = {x. \<exists>i\<in>mx. \<exists>j\<in>(Rxa R y). x = i \<plusminus> j}")
 apply (drule CollectD, (erule bexE)+,
        frule sym, thin_tac "1\<^sub>r = i \<plusminus> j")
 apply (drule CollectD, (erule bexE)+, rotate_tac -1,
        frule sym, thin_tac "1\<^sub>r = ia \<plusminus> ja")
 apply (frule_tac h = i in ideal_subset[of mx], assumption,
        frule_tac h = ia in ideal_subset[of mx], assumption,
        frule_tac h = j in ideal_subset, assumption+,
        frule_tac h = ja in ideal_subset, assumption+)
 apply (cut_tac ring_one)
 apply (frule_tac x = i and y = j in aGroup.ag_pOp_closed, assumption+)
 apply (frule_tac x = "i \<plusminus> j" and y = ia and z = ja in ring_distrib1,
           assumption+)
 apply (frule_tac x = ia and y = i and z = j in ring_distrib2, assumption+,
        frule_tac x = ja and y = i and z = j in ring_distrib2, assumption+,
        simp)
 apply (thin_tac "1\<^sub>r \<cdot>\<^sub>r ia = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia",
        thin_tac "1\<^sub>r \<cdot>\<^sub>r ja = i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja",
        simp add:ring_l_one[of "1\<^sub>r"])
 apply (frule_tac x = ia and r = i in ideal_ring_multiple[of mx], assumption+,
        frule_tac x = i and r = j in ideal_ring_multiple1[of mx], assumption+,
        frule_tac x = i and r = ja in ideal_ring_multiple1[of mx], assumption+,
        frule_tac r = j and x = ia in ideal_ring_multiple[of mx], assumption+)
 apply (subgoal_tac "j \<cdot>\<^sub>r ja \<in> mx")
 apply (frule_tac x = "i \<cdot>\<^sub>r ia" and y = "j \<cdot>\<^sub>r ia" in ideal_pOp_closed[of mx],
                   assumption+) apply (
        frule_tac x = "i \<cdot>\<^sub>r ja" and y = "j \<cdot>\<^sub>r ja" in ideal_pOp_closed[of mx],
           assumption+)
 apply (frule_tac x = "i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia" and y = "i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja" in
          ideal_pOp_closed[of mx], assumption+,
        thin_tac "i \<plusminus> j = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)",
        thin_tac "ia \<plusminus> ja = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)")
 apply (frule sym, thin_tac "1\<^sub>r = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)",
       simp)
 apply (simp add:maximal_ideal_def)

apply (thin_tac "i \<plusminus> j = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)",
       thin_tac "ia \<plusminus> ja = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)",
       thin_tac "i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja) \<in> carrier R",
       thin_tac "1\<^sub>r = i \<cdot>\<^sub>r ia \<plusminus> j \<cdot>\<^sub>r ia \<plusminus> (i \<cdot>\<^sub>r ja \<plusminus> j \<cdot>\<^sub>r ja)",
       thin_tac "i \<cdot>\<^sub>r j \<in> mx", thin_tac "i \<cdot>\<^sub>r ja \<in> mx",
       thin_tac "R \<diamondsuit>\<^sub>p y \<subseteq> carrier R", thin_tac "R \<diamondsuit>\<^sub>p x \<subseteq> carrier R",
       thin_tac "ideal R (R \<diamondsuit>\<^sub>p y)", thin_tac "ideal R (R \<diamondsuit>\<^sub>p x)")
 apply (simp add:Rxa_def, (erule bexE)+, simp)
 apply (simp add:ring_tOp_assoc)
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (frule_tac x = x and y = ra in ring_tOp_commute, assumption+, simp)
 apply (simp add:ring_tOp_assoc,
        frule_tac x = x and y = y in ring_tOp_closed, assumption+)
 apply (frule_tac x1 = r and y1 = ra and z1 = "x \<cdot>\<^sub>r y" in
        ring_tOp_assoc[THEN sym], assumption+, simp)
 apply (frule_tac x = r and y = ra in ring_tOp_closed, assumption+,
        rule ideal_ring_multiple[of mx], assumption+)
done

lemma (in Ring) chains_un:"\<lbrakk>c \<in> chains {I. ideal R I \<and> I \<subset> carrier R}; c \<noteq> {}\<rbrakk>
       \<Longrightarrow> ideal R (\<Union>c)"
apply (rule ideal_condition1)
apply (rule Union_least[of "c" "carrier R"])
 apply (simp add:chains_def,
       erule conjE,
       frule_tac c = X in subsetD[of "c" "{I. ideal R I \<and> I \<subset> carrier R}"],
       assumption+, simp add:psubset_imp_subset)
 apply (simp add:chains_def,
       erule conjE)
 apply (frule nonempty_ex[of "c"], erule exE)
 apply (frule_tac c = x in subsetD[of "c" "{I. ideal R I \<and> I \<subset> carrier R}"],
        assumption+, simp, erule conjE)
 apply (frule_tac I = x in ideal_zero, blast)

apply (rule ballI)+
 apply simp
 apply (erule bexE)+
apply (simp add: chains_def chain_subset_def)
 apply (frule conjunct1) apply (frule conjunct2)
 apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subset> carrier R} \<and> (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
 apply (frule_tac x = X in bspec, assumption,
        thin_tac "\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x",
        frule_tac x = Xa in bspec, assumption,
        thin_tac "\<forall>y\<in>c. X \<subseteq> y \<or> y \<subseteq> X")
 apply (frule_tac c = Xa in subsetD[of "c" "{I. ideal R I \<and> I \<subset> carrier R}"],
          assumption+,
        frule_tac c = X in subsetD[of "c" "{I. ideal R I \<and> I \<subset> carrier R}"],
          assumption+, simp)
 apply (erule conjE)+
 apply (erule disjE,
        frule_tac c = x and A = X and B = Xa in subsetD, assumption+,
        frule_tac x = x and y = y and I = Xa in ideal_pOp_closed, assumption+,
        blast)
 apply (frule_tac c = y and A = Xa and B = X in subsetD, assumption+,
        frule_tac x = x and y = y and I = X in ideal_pOp_closed, assumption+,
        blast)

apply (rule ballI)+
 apply (simp, erule bexE)
 apply (simp add:chains_def, erule conjE)
 apply (frule_tac c = X in subsetD[of "c" "{I. ideal R I \<and> I \<subset> carrier R}"],
        assumption+, simp, erule conjE)
 apply (frule_tac I = X and x = x and r = r in ideal_ring_multiple,
        assumption+, blast)
done

lemma (in Ring) zeroring_no_maximal:"zeroring R \<Longrightarrow> \<not> (\<exists>I. maximal_ideal R I)"
apply (rule contrapos_pp, simp+, erule exE,
       frule_tac mx = x in maximal_ideal_ideal)
apply (frule_tac I = x in ideal_zero)
apply (simp add:zeroring_def, erule conjE,
       cut_tac ring_one, simp, thin_tac "carrier R = {\<zero>}",
        frule sym, thin_tac "1\<^sub>r = \<zero>", simp, thin_tac "\<zero> = 1\<^sub>r")
apply (simp add:maximal_ideal_def)
done

lemma (in Ring) id_maximal_Exist:"\<not>(zeroring R) \<Longrightarrow> \<exists>I. maximal_ideal R I"
 apply (cut_tac A="{ I. ideal R I \<and> I \<subset> carrier R }" in Zorn_Lemma2)
 apply (rule ballI)

 apply (case_tac "C={}", simp)
   apply (cut_tac zero_ideal)
   apply (simp add:zeroring_def)
    apply (cut_tac Ring, simp,
           frule not_sym, thin_tac "carrier R \<noteq> {\<zero>}")
   apply (cut_tac ring_zero,
         frule singleton_sub[of "\<zero>" "carrier R"],
         thin_tac "\<zero> \<in> carrier R")
   apply (subst psubset_eq)
   apply blast
 apply (subgoal_tac "\<Union>C \<in> {I. ideal R I \<and> I \<subset> carrier R}")
 apply (subgoal_tac "\<forall>x\<in>C. x \<subseteq> (\<Union>C)", blast)
  apply (rule ballI, rule Union_upper, assumption)
  apply (simp add:chains_un)
  apply (cut_tac A = C in Union_least[of _ "carrier R"])
  apply (simp add:chains_def, erule conjE,
        frule_tac c = X and A = C in
          subsetD[of _ "{I. ideal R I \<and> I \<subset> carrier R}"], assumption+,
          simp add:ideal_subset1, simp add:psubset_eq)
  apply (rule contrapos_pp, simp+,
         cut_tac ring_one, frule sym, thin_tac "\<Union>C = carrier R")
  apply (frule_tac B = "\<Union>C" in eq_set_inc[of "1\<^sub>r" "carrier R"], assumption,
         thin_tac "carrier R = \<Union>C")
  apply (simp, erule bexE)
  apply (simp add:chains_def, erule conjE)
  apply (frule_tac c = X and A = C in
         subsetD[of _ "{I. ideal R I \<and> I \<subseteq> carrier R \<and> I \<noteq> carrier R}"],
         assumption+, simp, (erule conjE)+)
  apply (frule_tac I = X in ideal_inc_one, assumption+, simp)

 apply (erule bexE, simp, erule conjE)
 apply (subgoal_tac "maximal_ideal R M", blast)
 apply (simp add:maximal_ideal_def)

apply (rule conjI, rule contrapos_pp, simp+,
       frule_tac  I = M in ideal_inc_one, assumption+, simp)

apply (rule equalityI)
 apply (rule subsetI, simp)
 apply (erule conjE)
 apply (frule_tac x = x in spec,
        thin_tac "\<forall>x. ideal R x \<and> x \<subset> carrier R \<longrightarrow> M \<subseteq> x \<longrightarrow> x = M", simp)
 apply (frule_tac I = x in ideal_subset1, simp add:psubset_eq)
 apply (case_tac "x = carrier R", simp)
 apply simp

 apply (rule subsetI, simp)
 apply (erule disjE)
 apply simp
 apply (simp add:whole_ideal)
done

definition
  ideal_Int :: "[_, 'a set set] \<Rightarrow> 'a set" where
  "ideal_Int R S == \<Inter> S"

lemma (in Ring) ideal_Int_ideal:"\<lbrakk>S \<subseteq> {I. ideal R I}; S\<noteq>{}\<rbrakk> \<Longrightarrow>
                                                 ideal R (\<Inter> S)"
apply (rule ideal_condition1)
 apply (frule nonempty_ex[of "S"], erule exE)
 apply (frule_tac c = x in subsetD[of "S" "{I. ideal R I}"], assumption+)
 apply (simp, frule_tac I = x in ideal_subset1)
 apply (frule_tac B = x and A = S in Inter_lower)
 apply (rule_tac A = "\<Inter>S" and B = x and C = "carrier R" in subset_trans,
         assumption+)

 apply (cut_tac ideal_zero_forall, blast)
 apply (simp, rule ballI)

apply (rule ballI)+
 apply simp
 apply (frule_tac x = X in bspec, assumption,
        thin_tac "\<forall>X\<in>S. x \<in> X",
        frule_tac x = X in bspec, assumption,
        thin_tac "\<forall>X\<in>S. y \<in> X")
apply (frule_tac c = X in subsetD[of "S" "{I. ideal R I}"], assumption+,
       simp, rule_tac x = x and y = y in ideal_pOp_closed, assumption+)

apply (rule ballI)+
 apply (simp, rule ballI)
 apply (frule_tac x = X in bspec, assumption,
        thin_tac "\<forall>X\<in>S. x \<in> X",
        frule_tac c = X in subsetD[of "S" "{I. ideal R I}"], assumption+,
        simp add:ideal_ring_multiple)
done

lemma (in Ring) sum_prideals_Int:"\<lbrakk>\<forall>l \<le> n. f l \<in> carrier R;
                S = {I. ideal R I \<and> f ` {i. i \<le> n} \<subseteq> I}\<rbrakk> \<Longrightarrow>
                                  (sum_pr_ideals R f n) = \<Inter> S"
apply (rule equalityI)
apply (subgoal_tac "\<forall>X\<in>S. sum_pr_ideals R f n \<subseteq> X")
apply blast
 apply (rule ballI)
 apply (simp, erule conjE)
 apply (rule_tac I = X and n = n and f = f in sum_of_prideals4, assumption+)
apply (subgoal_tac "(sum_pr_ideals R f n) \<in> S")
 apply blast
 apply (simp add:CollectI)
 apply (simp add: sum_of_prideals2)
 apply (simp add: sum_of_prideals)
done

text\<open>This proves that \<open>(sum_pr_ideals R f n)\<close> is the smallest ideal containing
 \<open>f ` (Nset n)\<close>\<close>

primrec ideal_n_prod::"[('a, 'm) Ring_scheme, nat,  nat \<Rightarrow> 'a set] \<Rightarrow> 'a set"
where
  ideal_n_prod0: "ideal_n_prod R 0 J = J 0"
| ideal_n_prodSn: "ideal_n_prod R (Suc n) J =
                          (ideal_n_prod R n J) \<diamondsuit>\<^sub>r\<^bsub>R\<^esub> (J (Suc n))"

abbreviation
  IDNPROD  ("(3i\<Pi>\<^bsub>_,_\<^esub> _)" [98,98,99]98) where
  "i\<Pi>\<^bsub>R,n\<^esub> J == ideal_n_prod R n J"

primrec
  ideal_pow :: "['a set, ('a, 'more) Ring_scheme, nat] \<Rightarrow> 'a set"
               ("(3_/ \<^bsup>\<diamondsuit>_ _\<^esup>)" [120,120,121]120)
where
  ip0:  "I \<^bsup>\<diamondsuit>R 0\<^esup> = carrier R"
| ipSuc:  "I \<^bsup>\<diamondsuit>R (Suc n)\<^esup> = I \<diamondsuit>\<^sub>r\<^bsub>R\<^esub> (I \<^bsup>\<diamondsuit>R n\<^esup>)"

lemma (in Ring) prod_mem_prod_ideals:"\<lbrakk>ideal R I; ideal R J; i \<in> I; j \<in> J\<rbrakk> \<Longrightarrow>
                            i \<cdot>\<^sub>r j \<in> (I \<diamondsuit>\<^sub>r J)"
apply (simp add:ideal_prod_def)
apply (rule allI, rule impI, erule conjE, rename_tac X)
 apply (rule_tac A = "{x. \<exists>i\<in>I. \<exists>j\<in>J. x = Ring.tp R i j}" and B = X and c = "i \<cdot>\<^sub>r j" in  subsetD, assumption)
 apply simp apply blast
done

lemma (in Ring) ideal_prod_ideal:"\<lbrakk>ideal R I; ideal R J \<rbrakk> \<Longrightarrow>
                                        ideal R (I \<diamondsuit>\<^sub>r J)"
apply (rule ideal_condition1)
 apply (simp add:ideal_prod_def)
 apply (rule subsetI, simp)
 apply (cut_tac whole_ideal)
 apply (frule_tac x = "carrier R" in spec,
        thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> xa \<longrightarrow>
                                                                   x \<in> xa")
 apply (subgoal_tac "{x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> carrier R", simp)
     apply (thin_tac "ideal R (carrier R) \<and>
            {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> carrier R \<longrightarrow> x \<in> carrier R")
 apply (rule subsetI, simp, (erule bexE)+, simp)
 apply (frule_tac h = i in ideal_subset[of "I"], assumption+,
        frule_tac h = j in ideal_subset[of "J"], assumption+)
 apply (rule_tac x = i and y = j in ring_tOp_closed, assumption+)

 apply (frule ideal_zero[of "I"],
        frule ideal_zero[of "J"],
        subgoal_tac "\<zero> \<in> I \<diamondsuit>\<^sub>r\<^bsub> R\<^esub> J", blast)
 apply (simp add:ideal_prod_def)
 apply (rule allI, rule impI, erule conjE)
 apply (rule ideal_zero, assumption)

 apply (rule ballI)+
 apply (simp add:ideal_prod_def)
 apply (rule allI, rule impI)
 apply (frule_tac x = xa in spec,
        thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> xa
                                            \<longrightarrow> x \<in> xa",
        frule_tac x = xa in spec,
        thin_tac "\<forall>x. ideal R x \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> x \<longrightarrow> y \<in> x",
        erule conjE, simp,
        rule_tac x = x and y = y in ideal_pOp_closed, assumption+)
 apply (rule ballI)+
        apply (simp add:ideal_prod_def)
        apply (rule allI, rule impI, erule conjE)
        apply (frule_tac x = xa in spec,
               thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j}
                            \<subseteq> xa \<longrightarrow> x \<in> xa", simp)
 apply (simp add:ideal_ring_multiple)
done

lemma (in Ring) ideal_prod_commute:"\<lbrakk>ideal R I; ideal R J\<rbrakk> \<Longrightarrow>
                                              I \<diamondsuit>\<^sub>r J = J \<diamondsuit>\<^sub>r I"
apply (simp add:ideal_prod_def)
apply (subgoal_tac "{K. ideal R K \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j}
       \<subseteq> K}  = {K. ideal R K \<and> {x. \<exists>i\<in>J. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j} \<subseteq> K}")
apply simp
apply (rule equalityI)
apply (rule subsetI, rename_tac X, simp, erule conjE)
 apply (rule subsetI, simp)
 apply ((erule bexE)+)
 apply (subgoal_tac "x \<in> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j}",
        rule_tac c = x and A = "{x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j}" and B = X in
        subsetD, assumption+,
        frule_tac h = i in ideal_subset[of "J"], assumption,
        frule_tac h = j in ideal_subset[of "I"], assumption,
        frule_tac x = i and y = j in ring_tOp_commute, assumption+, simp,
        blast)
 apply (rule subsetI, simp, erule conjE,
        rule subsetI, simp,
        (erule bexE)+,
        subgoal_tac "xa \<in> {x. \<exists>i\<in>J. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j}",
        rule_tac c = xa and A = "{x. \<exists>i\<in>J. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j}" and B = x in
                 subsetD, assumption+,
        frule_tac h = i in ideal_subset[of "I"], assumption,
        frule_tac h = j in ideal_subset[of "J"], assumption,
        frule_tac x = i and y = j in ring_tOp_commute, assumption+, simp,
        blast)
done

lemma (in Ring) ideal_prod_subTr:"\<lbrakk>ideal R I; ideal R J; ideal R C;
                        \<forall>i\<in>I. \<forall>j\<in>J. i \<cdot>\<^sub>r j \<in> C\<rbrakk> \<Longrightarrow> I \<diamondsuit>\<^sub>r J \<subseteq> C"
apply (simp add:ideal_prod_def)
 apply (rule_tac B = C and
        A = "{L. ideal R L \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>r j} \<subseteq> L}" in
        Inter_lower)
 apply simp
 apply (rule subsetI, simp, (erule bexE)+, simp)
done

lemma (in Ring) n_prod_idealTr:
     "(\<forall>k \<le> n. ideal R (J k)) \<longrightarrow> ideal R (ideal_n_prod R n J)"
apply (induct_tac n)
apply (rule impI)
apply simp

apply (rule impI)
apply (simp only:ideal_n_prodSn)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (rule ideal_prod_ideal, assumption)
 apply simp
done

lemma (in Ring) n_prod_ideal:"\<lbrakk>\<forall>k \<le> n. ideal R (J k)\<rbrakk>
                               \<Longrightarrow>  ideal R (ideal_n_prod R n J)"
apply (simp add:n_prod_idealTr)
done

lemma (in Ring) ideal_prod_la1:"\<lbrakk>ideal R I; ideal R J\<rbrakk> \<Longrightarrow> (I \<diamondsuit>\<^sub>r J) \<subseteq> I"
 apply (simp add:ideal_prod_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "{x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>r j} \<subseteq> I")
 apply blast
apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>r j} \<subseteq> xa
                                                              \<longrightarrow> x \<in> xa")
 apply (rule subsetI, simp add:CollectI,
        (erule bexE)+, frule_tac h = j in ideal_subset[of "J"], assumption+)
 apply (simp add:ideal_ring_multiple1)
done

lemma (in Ring) ideal_prod_el1:"\<lbrakk>ideal R I; ideal R J; a \<in> (I \<diamondsuit>\<^sub>r J)\<rbrakk> \<Longrightarrow>
                           a \<in> I"
apply (frule ideal_prod_la1 [of "I" "J"], assumption+)
apply (rule subsetD, assumption+)
done

lemma (in Ring) ideal_prod_la2:"\<lbrakk>ideal R I; ideal R J \<rbrakk> \<Longrightarrow> (I \<diamondsuit>\<^sub>r J) \<subseteq> J"
 apply (subst ideal_prod_commute, assumption+,
        rule ideal_prod_la1[of "J" "I"], assumption+)
done

lemma (in Ring) ideal_prod_sub_Int:"\<lbrakk>ideal R I; ideal R J \<rbrakk> \<Longrightarrow>
                     (I \<diamondsuit>\<^sub>r J) \<subseteq> I \<inter> J"
by (simp add:ideal_prod_la1 ideal_prod_la2)

lemma (in Ring) ideal_prod_el2:"\<lbrakk>ideal R I; ideal R J; a \<in> (I \<diamondsuit>\<^sub>r J)\<rbrakk> \<Longrightarrow>
                                 a \<in> J"
by (frule ideal_prod_la2 [of "I" "J"], assumption+,
       rule subsetD, assumption+)

text\<open>\<open>i\<Pi>\<^bsub>R,n\<^esub> J\<close> is the product of ideals\<close>
lemma (in Ring) ele_n_prodTr0:"\<lbrakk>\<forall>k \<le> (Suc n). ideal R (J k);
             a \<in> i\<Pi>\<^bsub>R,(Suc n)\<^esub> J \<rbrakk> \<Longrightarrow> a \<in> (i\<Pi>\<^bsub>R,n\<^esub> J) \<and> a \<in> (J (Suc n))"
apply (simp add:Nset_Suc[of n])
 apply (cut_tac n_prod_ideal[of n J])
apply (rule conjI)
 apply (rule ideal_prod_el1 [of "i\<Pi>\<^bsub>R,n\<^esub> J" "J (Suc n)"], assumption, simp+)
 apply (rule ideal_prod_el2[of "i\<Pi>\<^bsub>R,n\<^esub> J" "J (Suc n)"], assumption+, simp+)
done

lemma (in Ring) ele_n_prodTr1:
      "(\<forall>k \<le> n. ideal R (J k)) \<and> a \<in> ideal_n_prod R n J \<longrightarrow>
                                             (\<forall>k \<le> n. a \<in> (J k))"
apply (induct_tac n)
(** n = 0 **)
 apply simp
(** n **)
 apply (rule impI)
 apply (rule allI, rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (erule conjE)
 apply (frule_tac n = n in ele_n_prodTr0[of _ J a])
 apply simp

 apply (erule conjE,
        thin_tac "\<forall>k\<le>Suc n. ideal R (J k)")
 apply simp
 apply (case_tac "k = Suc n", simp)
 apply (frule_tac m = k and n = "Suc n" in noteq_le_less, assumption+,
        thin_tac "k \<le> Suc n")
 apply (frule_tac x = k and n = "Suc n" in less_le_diff, simp)
done

lemma (in Ring) ele_n_prod:"\<lbrakk>\<forall>k \<le> n. ideal R (J k);
                       a \<in> ideal_n_prod R n J \<rbrakk> \<Longrightarrow>  \<forall>k \<le> n. a \<in> (J k)"
by (simp add: ele_n_prodTr1 [of "n" "J" "a"])

lemma (in Ring) idealprod_whole_l:"ideal R I \<Longrightarrow> (carrier R) \<diamondsuit>\<^sub>r\<^bsub>R\<^esub> I = I"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ideal_prod_def)
 apply (subgoal_tac "{x. \<exists>i\<in>carrier R. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j} \<subseteq> I")
 apply blast
 apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>carrier R. \<exists>j\<in>I.
                       x = i \<cdot>\<^sub>r j} \<subseteq> xa \<longrightarrow> x \<in> xa")
 apply (rule subsetI)
 apply simp
 apply ((erule bexE)+, simp)
 apply (thin_tac "xa = i \<cdot>\<^sub>r j", simp add:ideal_ring_multiple)
apply (rule subsetI)
 apply (simp add:ideal_prod_def)
 apply (rule allI, rule impI) apply (erule conjE)
 apply (rename_tac xa X)
 apply (cut_tac ring_one)
 apply (frule_tac h = xa in ideal_subset[of "I"], assumption,
        frule_tac x = xa in ring_l_one)
 apply (subgoal_tac "1\<^sub>r \<cdot>\<^sub>r xa \<in> {x. \<exists>i\<in>carrier R. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j}")
 apply (rule_tac c = xa and A = "{x. \<exists>i\<in>carrier R. \<exists>j\<in>I. x = i \<cdot>\<^sub>r j}" and
         B = X in subsetD, assumption+)
 apply simp
 apply simp
 apply (frule sym, thin_tac "1\<^sub>r \<cdot>\<^sub>r xa = xa", blast)
done

lemma (in Ring) idealprod_whole_r:"ideal R I \<Longrightarrow> I \<diamondsuit>\<^sub>r (carrier R) = I"
by (cut_tac whole_ideal,
       simp add:ideal_prod_commute[of "I" "carrier R"],
       simp add:idealprod_whole_l)

lemma (in Ring) idealpow_1_self:"ideal R I \<Longrightarrow> I \<^bsup>\<diamondsuit>R (Suc 0)\<^esup> = I"
apply simp
apply (simp add:idealprod_whole_r)
done

lemma (in Ring) ideal_pow_ideal:"ideal R I \<Longrightarrow> ideal R (I \<^bsup>\<diamondsuit>R n\<^esup>)"
apply (induct_tac n)
apply (simp add:whole_ideal)
apply simp
apply (simp add:ideal_prod_ideal)
done

lemma (in Ring) ideal_prod_prime:"\<lbrakk>ideal R I; ideal R J; prime_ideal R P;
                          I \<diamondsuit>\<^sub>r J \<subseteq> P \<rbrakk> \<Longrightarrow> I \<subseteq> P \<or> J \<subseteq> P"
apply (rule contrapos_pp, simp+)
apply (erule conjE, simp add:subset_eq, (erule bexE)+)
apply (frule_tac i = x and j = xa in prod_mem_prod_ideals[of "I" "J"],
          assumption+)
 apply (frule_tac x = "x \<cdot>\<^sub>r xa" in bspec, assumption,
        thin_tac "\<forall>x\<in>I \<diamondsuit>\<^sub>r\<^bsub> R\<^esub> J. x \<in> P")
 apply (simp add: prime_ideal_def, (erule conjE)+)
 apply (frule_tac h = x in ideal_subset, assumption,
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P",
        frule_tac h = xa in ideal_subset, assumption,
        frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P",
        simp)
done

lemma (in Ring) ideal_n_prod_primeTr:"prime_ideal R P \<Longrightarrow>
       (\<forall>k \<le> n. ideal R (J k)) \<longrightarrow> (ideal_n_prod R n J \<subseteq> P) \<longrightarrow>
                                               (\<exists>i \<le> n. (J i) \<subseteq> P)"
apply (induct_tac n)
apply simp

apply (rule impI)
 apply (rule impI, simp)
 apply (cut_tac I = "i\<Pi>\<^bsub>R,n\<^esub> J" and J = "J (Suc n)" in
                      ideal_prod_prime[of _ _ "P"],
        rule_tac n = n and J = J in n_prod_ideal,
         rule allI, simp+)
 apply (erule disjE, simp)
 apply (cut_tac n = n in Nsetn_sub_mem1,
        blast)
 apply blast
done

lemma (in Ring) ideal_n_prod_prime:"\<lbrakk>prime_ideal R P;
            \<forall>k \<le> n. ideal R (J k); ideal_n_prod R n J \<subseteq> P\<rbrakk> \<Longrightarrow>
                                            \<exists>i \<le> n. (J i) \<subseteq> P"
apply (simp add:ideal_n_prod_primeTr)
done

definition
  ppa::"[_, nat \<Rightarrow> 'a set, 'a set, nat] \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "ppa R P A i l = (SOME x. x \<in> A \<and> x \<in> (P (skip i l)) \<and> x \<notin> P i)"
     (** Note (ppa R P A) is used to prove prime_ideal_cont1,
         some element x of A such that x \<in> P j for (i \<noteq> j) and x \<notin> P i **)

lemma (in Ring) prod_primeTr:"\<lbrakk>prime_ideal R P; ideal R A; \<not> A \<subseteq> P;
                ideal R B; \<not> B \<subseteq> P \<rbrakk> \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B \<and> x \<notin> P"
apply (simp add:subset_eq)
 apply (erule bexE)+
apply (subgoal_tac "x \<cdot>\<^sub>r xa \<in> A \<and> x \<cdot>\<^sub>r xa \<in> B \<and> x \<cdot>\<^sub>r xa \<notin> P")
 apply blast
 apply (rule conjI)
 apply (rule ideal_ring_multiple1, assumption+)
  apply (simp add:ideal_subset)
 apply (rule conjI)
  apply (rule ideal_ring_multiple, assumption+)
  apply (simp add:ideal_subset)

 apply (rule contrapos_pp, simp+)
apply (simp add:prime_ideal_def, (erule conjE)+)
 apply (frule_tac h = x in ideal_subset[of "A"], assumption+,
        frule_tac h = xa in ideal_subset[of "B"], assumption+,
        frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P",
        frule_tac x = xa in bspec, assumption,
        thin_tac "\<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P")
  apply simp
done

lemma (in Ring) prod_primeTr1:"\<lbrakk>\<forall>k \<le> (Suc n). prime_ideal R (P k);
       ideal R A; \<forall>l \<le> (Suc n). \<not> (A \<subseteq> P l);
       \<forall>k \<le> (Suc n). \<forall>l \<le> (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l); i \<le> (Suc n)\<rbrakk> \<Longrightarrow>
       \<forall>l \<le> n. ppa R P A i l \<in> A \<and>
                  ppa R P A i l \<in> (P (skip i l)) \<and> ppa R P A i l \<notin> (P i)"
apply (rule allI, rule impI)
apply (cut_tac i = i and l = l in skip_il_neq_i)
apply (rotate_tac 2)
      apply (frule_tac x = i in spec,
             thin_tac "\<forall>l \<le> (Suc n). \<not> A \<subseteq> P l", simp)

      apply (cut_tac l = l in skip_mem[of _ "n" "i"], simp,
             frule_tac x = "skip i l" in spec,
             thin_tac "\<forall>k \<le> (Suc n). \<forall>l \<le> (Suc n). k = l \<or> \<not> P k \<subseteq> P l",
             simp)
     apply (rotate_tac -1,
            frule_tac x = i in spec,
            thin_tac "\<forall>la \<le> (Suc n). skip i l = la \<or> \<not> P (skip i l) \<subseteq> P la",
            simp)
apply (cut_tac P = "P i" and A = A and B = "P (skip i l)" in prod_primeTr,
       simp, assumption+)
 apply (frule_tac x = "skip i l" in spec,
        thin_tac "\<forall>k\<le>Suc n. prime_ideal R (P k)", simp,
        rule prime_ideal_ideal, assumption+)
 apply (simp add:ppa_def)
 apply (rule someI2_ex, assumption+)
done

lemma (in Ring) ppa_mem:"\<lbrakk>\<forall>k \<le> (Suc n). prime_ideal R (P k); ideal R A;
      \<forall>l \<le> (Suc n). \<not> (A \<subseteq> P l);
      \<forall>k \<le> (Suc n). \<forall>l \<le> (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l);
      i  \<le> (Suc n); l \<le> n\<rbrakk> \<Longrightarrow> ppa R P A i l \<in> carrier R"
apply (frule_tac prod_primeTr1[of n P A], assumption+)
 apply (rotate_tac -1, frule_tac x = l in spec,
        thin_tac "\<forall>l\<le>n. ppa R P A i l \<in> A \<and>
           ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i", simp)
 apply (simp add:ideal_subset)
done

lemma (in Ring) nsum_memrTr:"(\<forall>i \<le> n. f i \<in> carrier R) \<longrightarrow>
                             (\<forall>l \<le> n. nsum R f l \<in> carrier R)"
apply (cut_tac ring_is_ag)
apply (induct_tac n)
(** n = 0 **)
 apply (rule impI, rule allI, rule impI)
 apply simp
(** n **)
apply (rule impI)
 apply (rule allI, rule impI)

 apply (rule aGroup.nsum_mem, assumption)
 apply (rule allI, simp)
done

lemma (in Ring) nsum_memr:"\<forall>i \<le> n. f i \<in> carrier R \<Longrightarrow>
                          \<forall>l \<le> n. nsum R f l \<in> carrier R"
by (simp add:nsum_memrTr)

lemma (in Ring) nsum_ideal_incTr:"ideal R A \<Longrightarrow>
               (\<forall>i \<le> n. f i \<in> A) \<longrightarrow>  nsum R f n \<in> A"
 apply (induct_tac n)
 apply (rule impI)
  apply simp
(** n **)
apply (rule impI)
apply simp
apply (rule ideal_pOp_closed, assumption+)
 apply simp
done

lemma (in Ring) nsum_ideal_inc:"\<lbrakk>ideal R A; \<forall>i \<le> n. f i \<in> A\<rbrakk> \<Longrightarrow>
                    nsum R f n \<in> A"
by (simp add:nsum_ideal_incTr)

lemma (in Ring) nsum_ideal_excTr:"ideal R A \<Longrightarrow>
      (\<forall>i \<le> n. f i \<in> carrier R) \<and> (\<exists>j \<le> n. (\<forall>l \<in> {i. i \<le> n} -{j}. f l \<in> A)
       \<and> (f j \<notin> A)) \<longrightarrow> nsum R f n \<notin> A"
apply (induct_tac n)
(** n = 0 **)
 apply simp
(** n **)
 apply (rule impI)
 apply (erule conjE)+
apply (erule exE)
apply (case_tac "j = Suc n", simp) apply (
       thin_tac "(\<exists>j\<le>n. f j \<notin> A) \<longrightarrow> \<Sigma>\<^sub>e R f n \<notin> A")
 apply (erule conjE)
 apply (cut_tac n = n and f = f in nsum_ideal_inc[of A], assumption,
        rule allI, simp)
 apply (rule contrapos_pp, simp+)
 apply (frule_tac a = "\<Sigma>\<^sub>e R f n" and b = "f (Suc n)" in
                   ideal_ele_sumTr1[of A],
        simp add:ideal_subset, simp, assumption+, simp)

apply (erule conjE,
       frule_tac m = j and n = "Suc n" in noteq_le_less, assumption,
       frule_tac x = j and n = "Suc n" in less_le_diff,
       thin_tac "j \<le> Suc n", thin_tac "j < Suc n", simp,
       cut_tac n = n in Nsetn_sub_mem1, simp)
apply (erule conjE,
       frule_tac x = "Suc n" in bspec, simp)
apply (rule contrapos_pp, simp+)
 apply (frule_tac a = "\<Sigma>\<^sub>e R f n" and b = "f (Suc n)" in
                   ideal_ele_sumTr2[of A])
 apply (cut_tac ring_is_ag,
        rule_tac n = n in aGroup.nsum_mem[of R _ f], assumption+,
        rule allI, simp, simp, assumption+, simp)
 apply (subgoal_tac "\<exists>j\<le>n. (\<forall>l\<in>{i. i \<le> n} - {j}. f l \<in> A) \<and> f j \<notin> A",
        simp,
        thin_tac "(\<exists>j\<le>n. (\<forall>l\<in>{i. i \<le> n} - {j}. f l \<in> A) \<and> f j \<notin> A)
                     \<longrightarrow> \<Sigma>\<^sub>e R f n \<notin> A")
 apply (subgoal_tac "\<forall>l\<in>{i. i \<le> n} - {j}. f l \<in> A", blast,
        thin_tac "\<Sigma>\<^sub>e R f n \<plusminus> f (Suc n) \<in> A",
        thin_tac "\<Sigma>\<^sub>e R f n \<in> A")
 apply (rule ballI)
 apply (frule_tac x = l in bspec, simp, assumption)
done

lemma (in Ring) nsum_ideal_exc:"\<lbrakk>ideal R A; \<forall>i \<le> n. f i \<in> carrier R;
      \<exists>j \<le> n. (\<forall>l\<in>{i. i \<le> n} -{j}. f l \<in> A) \<and> (f j \<notin> A) \<rbrakk> \<Longrightarrow> nsum R f n \<notin> A"
by (simp add:nsum_ideal_excTr)

lemma (in Ring) nprod_memTr:"(\<forall>i \<le> n. f i \<in> carrier R) \<longrightarrow>
                             (\<forall>l. l \<le> n \<longrightarrow>  nprod R f l \<in> carrier R)"
apply (induct_tac n)
apply (rule impI, rule allI, rule impI, simp)

apply (rule impI, rule allI, rule impI)
apply (case_tac "l \<le> n")
 apply (cut_tac n = n in Nset_Suc, blast)
 apply (cut_tac m = l and n = "Suc n" in Nat.le_antisym, assumption)
 apply (simp add: not_less)
 apply simp
 apply (rule ring_tOp_closed, simp)
 apply (cut_tac n = n in Nset_Suc, blast)
done

lemma (in Ring) nprod_mem:"\<lbrakk>\<forall>i \<le> n. f i \<in> carrier R; l \<le> n\<rbrakk> \<Longrightarrow>
                              nprod R f l \<in> carrier R"
by (simp add:nprod_memTr)

lemma (in Ring) ideal_nprod_incTr:"ideal R A \<Longrightarrow>
                (\<forall>i \<le> n. f i \<in> carrier R) \<and>
                             (\<exists>l \<le> n. f l \<in> A) \<longrightarrow> nprod R f n \<in> A"
apply (induct_tac n)
(** n = 0 **)
apply simp
(** n **)
apply (rule impI)
 apply (erule conjE)+
apply simp
 apply (erule exE)
 apply (case_tac "l = Suc n", simp)
 apply (rule_tac x = "f (Suc n)" and r = "nprod R f n" in
                 ideal_ring_multiple[of "A"], assumption+)
 apply (rule_tac n = "Suc n" and f = f and l = n in nprod_mem,
                 assumption+, simp)
 apply (erule conjE)
 apply (frule_tac m = l and n = "Suc n" in noteq_le_less, assumption,
       frule_tac x = l and n = "Suc n" in less_le_diff,
       thin_tac "l \<le> Suc n", thin_tac "l < Suc n", simp)
apply (rule_tac x = "nprod R f n" and r = "f (Suc n)" in
                      ideal_ring_multiple1[of "A"], assumption+)
 apply blast
 apply simp
done

lemma (in Ring) ideal_nprod_inc:"\<lbrakk>ideal R A; \<forall>i \<le> n. f i \<in> carrier R;
                \<exists>l \<le> n. f l \<in> A\<rbrakk> \<Longrightarrow> nprod R f n \<in> A"
by (simp add:ideal_nprod_incTr)

lemma (in Ring) nprod_excTr:"prime_ideal R P \<Longrightarrow>
          (\<forall>i \<le> n. f i \<in> carrier R) \<and> (\<forall>l \<le> n. f l \<notin> P) \<longrightarrow>
                                                     nprod R f n \<notin> P"
apply (induct_tac n)
(** n = 0 **)
 apply simp  (* n = 0 done *)
(** n **)
apply (rule impI)
apply (erule conjE)+
 apply simp
  apply (rule_tac y = "f (Suc n)" and x = "nprod R f n" in
          prime_elems_mult_not[of "P"], assumption,
         rule_tac n = n in  nprod_mem, rule allI, simp+)
done

lemma (in Ring) prime_nprod_exc:"\<lbrakk>prime_ideal R P; \<forall>i \<le> n. f i \<in> carrier R;
                \<forall>l \<le> n. f l \<notin> P\<rbrakk> \<Longrightarrow> nprod R f n \<notin> P"
by (simp add:nprod_excTr)

definition
  nilrad :: "_ \<Rightarrow> 'a set" where
  "nilrad R = {x. x \<in> carrier R \<and> nilpotent R x}"

lemma (in Ring) id_nilrad_ideal:"ideal R (nilrad R)"
apply (cut_tac ring_is_ag)
apply (rule ideal_condition1[of "nilrad R"])
 apply (rule subsetI) apply (simp add:nilrad_def CollectI)
 apply (simp add:nilrad_def)
 apply (cut_tac ring_zero)
 apply (subgoal_tac "nilpotent R \<zero>")
 apply blast
 apply (simp add:nilpotent_def)
 apply (frule np_1[of "\<zero>"], blast)

 apply (rule ballI)+
apply (simp add:nilrad_def nilpotent_def, (erule conjE)+)
 apply (erule exE)+
 apply (simp add:aGroup.ag_pOp_closed[of "R"])
 apply (frule_tac x = x and y = y and m = n and n = na in npAdd,
        assumption+, blast)

 apply (rule ballI)+
 apply (simp add:nilrad_def nilpotent_def, erule conjE, erule exE)
 apply (simp add:ring_tOp_closed,
        frule_tac x = r and y = x and n = n in npMul, assumption+,
           simp,
        frule_tac x = r and n = n in npClose)
        apply (simp add:ring_times_x_0, blast)
done

definition
  rad_ideal :: "[_, 'a set ] \<Rightarrow> 'a set" where
  "rad_ideal R I = {a. a \<in> carrier R \<and> nilpotent (qring R I) ((pj R I) a)}"

lemma (in Ring) id_rad_invim:"ideal R I \<Longrightarrow>
       rad_ideal R I = (rInvim R (qring R I) (pj R I ) (nilrad (qring R I)))"
apply (cut_tac ring_is_ag)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:rad_ideal_def)
 apply (erule conjE)+
 apply (simp add:rInvim_def)
 apply (simp add:nilrad_def)
 apply (subst pj_mem, rule Ring_axioms)
 apply assumption+
 apply (simp add:qring_def ar_coset_def set_rcs_def)
 apply (simp add:aGroup.ag_carrier_carrier)
 apply blast

apply (rule subsetI)
 apply (simp add:rInvim_def nilrad_def)
apply (simp add: rad_ideal_def)
done

lemma (in Ring) id_rad_ideal:"ideal R I \<Longrightarrow> ideal R (rad_ideal R I)"
(* thm invim_of_ideal *)
apply (subst id_rad_invim [of "I"], assumption)
apply (rule invim_of_ideal, rule Ring_axioms, assumption)
apply (rule Ring.id_nilrad_ideal)
apply (simp add:qring_ring)
done

lemma (in Ring) id_rad_cont_I:"ideal R I \<Longrightarrow> I \<subseteq> (rad_ideal R I)"
apply (simp add:rad_ideal_def)
apply (rule subsetI, simp,
       simp add:ideal_subset)
apply (simp add:nilpotent_def)
apply (subst pj_mem, rule Ring_axioms, assumption+,
       simp add:ideal_subset) (* thm npQring *)

 apply (frule_tac h = x in ideal_subset[of "I"], assumption,
        frule_tac a = x in npQring[OF Ring, of "I" _ "Suc 0"], assumption,
        simp only:np_1, simp only:Qring_fix1,
        subst qring_zero[of "I"], assumption)
 apply blast
done

lemma (in Ring) id_rad_set:"ideal R I \<Longrightarrow>
       rad_ideal R I = {x. x \<in> carrier R \<and> (\<exists>n. npow R x n \<in> I)}"
apply (simp add:rad_ideal_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:nilpotent_def, erule conjE, erule exE)
 apply (simp add: pj_mem[OF Ring], simp add:npQring[OF Ring])
apply ( simp add:qring_zero)
 apply (frule_tac x = x and n = n in npClose)
 apply (frule_tac a = "x^\<^bsup>R n\<^esup>" in ar_coset_same3[of "I"], assumption+,
        blast)
apply (rule subsetI, simp, erule conjE, erule exE)
 apply (simp add:nilpotent_def)
 apply (simp add: pj_mem[OF Ring], simp add:npQring[OF Ring],
                                            simp add:qring_zero)
 apply (frule_tac a = "x^\<^bsup>R n\<^esup>" in ar_coset_same4[of "I"], assumption+)
 apply blast
done

lemma (in Ring) rad_primary_prime:"primary_ideal R q \<Longrightarrow>
                                    prime_ideal R (rad_ideal R q)"
apply (simp add:prime_ideal_def)
apply (frule primary_ideal_ideal[of "q"])
apply (simp add:id_rad_ideal)
apply (rule conjI)
 apply (rule contrapos_pp, simp+)
 apply (simp add:id_rad_set, erule conjE, erule exE)
 apply (simp add:npOne)
 apply (simp add:primary_ideal_proper1[of "q"])

apply ((rule ballI)+, rule impI)
 apply (rule contrapos_pp, simp+, erule conjE)
 apply (simp add:id_rad_set, erule conjE, erule exE)
 apply (simp add:npMul)
 apply (simp add:primary_ideal_def, (erule conjE)+)
 apply (frule_tac x = x and n = n in npClose,
        frule_tac x = y and n = n in npClose)
 apply (frule_tac x = "x^\<^bsup>R n\<^esup>" in bspec, assumption,
        thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. x \<cdot>\<^sub>r y \<in> q \<longrightarrow>
                                    (\<exists>n. x^\<^bsup>R n\<^esup> \<in> q) \<or> y \<in> q",
        frule_tac x = "y^\<^bsup>R n\<^esup>" in bspec, assumption,
        thin_tac "\<forall>y\<in>carrier R. x^\<^bsup>R n\<^esup> \<cdot>\<^sub>r y \<in> q \<longrightarrow>
                             (\<exists>na. x^\<^bsup>R n\<^esup>^\<^bsup>R na\<^esup> \<in> q) \<or> y \<in> q", simp)
 apply (simp add:npMulExp)
done

lemma (in Ring) npow_notin_prime:"\<lbrakk>prime_ideal R P; x \<in> carrier R; x \<notin> P\<rbrakk>
                                \<Longrightarrow> \<forall>n. npow R x n \<notin> P"
apply (rule allI)
apply (induct_tac n)
 apply simp
 apply (simp add:prime_ideal_proper1)

 apply simp
 apply (frule_tac x = x and n = na in npClose)
 apply (simp add:prime_elems_mult_not)
done

lemma (in Ring) npow_in_prime:"\<lbrakk>prime_ideal R P; x \<in> carrier R;
                               \<exists>n. npow R x n \<in> P \<rbrakk> \<Longrightarrow> x \<in> P"
apply (rule contrapos_pp, simp+)
apply (frule npow_notin_prime, assumption+)
apply blast
done

definition
  mul_closed_set::"[_, 'a set ] \<Rightarrow> bool" where
  "mul_closed_set R S \<longleftrightarrow> S \<subseteq> carrier R \<and> (\<forall>s\<in>S. \<forall>t\<in>S. s \<cdot>\<^sub>r\<^bsub>R\<^esub> t \<in> S)"

locale Idomain = Ring +
       assumes idom:
       "\<lbrakk>a \<in> carrier R; b \<in> carrier R; a \<cdot>\<^sub>r b = \<zero>\<rbrakk> \<Longrightarrow> a = \<zero> \<or> b = \<zero>"
  (* integral domain *)

locale Corps =
       fixes K (structure)
       assumes f_is_ring: "Ring K"
       and f_inv: "\<forall>x\<in>carrier K - {\<zero>}. \<exists>x' \<in> carrier K. x' \<cdot>\<^sub>r x = 1\<^sub>r"
  (** integral domain **)

lemma (in Ring) mul_closed_set_sub:"mul_closed_set R S \<Longrightarrow> S \<subseteq> carrier R"
by (simp add:mul_closed_set_def)

lemma (in Ring) mul_closed_set_tOp_closed:"\<lbrakk>mul_closed_set R S; s \<in> S;
                            t \<in> S\<rbrakk> \<Longrightarrow> s \<cdot>\<^sub>r t \<in> S"
by (simp add:mul_closed_set_def)

lemma (in Corps) f_inv_unique:"\<lbrakk> x \<in> carrier K - {\<zero>}; x' \<in> carrier K;
      x'' \<in> carrier K; x' \<cdot>\<^sub>r  x = 1\<^sub>r; x'' \<cdot>\<^sub>r x = 1\<^sub>r \<rbrakk> \<Longrightarrow> x' = x''"
apply (cut_tac  f_is_ring)
 apply (cut_tac x = x' and y = x and z = x'' in Ring.ring_tOp_assoc[of K],
        assumption+, simp, assumption, simp)
 apply (simp add:Ring.ring_l_one[of K],
        simp add:Ring.ring_tOp_commute[of K x x''] Ring.ring_r_one[of K])
done

definition
  invf :: "[_, 'a] \<Rightarrow> 'a" where
  "invf K x = (THE y. y \<in> carrier K \<and> y \<cdot>\<^sub>r\<^bsub>K\<^esub> x = 1\<^sub>r\<^bsub>K\<^esub>)"

lemma (in Corps) invf_inv:"x \<in> carrier K - {\<zero>} \<Longrightarrow>
                (invf K x) \<in> carrier K \<and> (invf K x) \<cdot>\<^sub>r x = 1\<^sub>r "
apply (simp add:invf_def)
apply (rule theI')
apply (rule ex_ex1I)
apply (cut_tac f_inv, blast)
apply (rule_tac x' = xa and x'' = y in f_inv_unique[of x])
       apply simp+
done



definition
  npowf :: "_  \<Rightarrow> 'a \<Rightarrow> int  \<Rightarrow> 'a" where
  "npowf K x n =
    (if 0 \<le> n then npow K x (nat n) else npow K (invf K x) (nat (- n)))"

abbreviation
  NPOWF ::  "['a, _, int] \<Rightarrow>  'a"  ("(3_\<^bsub>_\<^esub>\<^bsup>_\<^esup>)" [77,77,78]77) where
  "a\<^bsub>K\<^esub>\<^bsup>n\<^esup> == npowf K a n"

abbreviation
  IOP :: "['a, _] \<Rightarrow> 'a" ("(_\<^bsup>\<hyphen> _\<^esup>)" [87,88]87) where
  "a\<^bsup>\<hyphen>K\<^esup> == invf K a"

lemma (in Idomain) idom_is_ring: "Ring R" ..

lemma (in Idomain) idom_tOp_nonzeros:"\<lbrakk>x \<in> carrier R;
       y \<in> carrier R; x \<noteq> \<zero>;  y \<noteq> \<zero>\<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>r y \<noteq> \<zero>"
apply (rule contrapos_pp, simp+)
apply (cut_tac idom[of x y]) apply (erule disjE, simp+)
done

lemma (in Idomain) idom_potent_nonzero:
       "\<lbrakk>x \<in> carrier R; x \<noteq> \<zero>\<rbrakk>  \<Longrightarrow> npow R x n \<noteq> \<zero> "
apply (induct_tac n)
 apply simp  (* case 0 *)
 apply (rule contrapos_pp, simp+)
 apply (frule ring_l_one[of "x", THEN sym]) apply simp
 apply (simp add:ring_times_0_x)
 (* case (Suc n) *)

 apply (rule contrapos_pp, simp+)
 apply (frule_tac n = n in npClose[of x],
        cut_tac a = "x^\<^bsup>R n\<^esup>" and b = x in idom, assumption+)
 apply (erule disjE, simp+)
done

lemma (in Idomain) idom_potent_unit:"\<lbrakk>a \<in> carrier R; 0 < n\<rbrakk>
                 \<Longrightarrow> (Unit R a) = (Unit R (npow R a n))"
apply (rule iffI)
 apply (simp add:Unit_def, erule bexE)
 apply (simp add:npClose)
 apply (frule_tac x1 = a and y1 = b and n1 = n in npMul[THEN sym], assumption,
        simp add:npOne)
  apply (frule_tac x = b and n = n in npClose, blast)

apply (case_tac "n = Suc 0", simp only: np_1)
 apply (simp add:Unit_def, erule conjE, erule bexE)
 apply (cut_tac x = a and n = "n - Suc 0" in npow_suc[of R], simp del:npow_suc,
      thin_tac "a^\<^bsup>R n\<^esup> = a^\<^bsup>R (n - Suc 0)\<^esup> \<cdot>\<^sub>r a",
      frule_tac x = a and n = "n - Suc 0" in npClose,
      frule_tac x = "a^\<^bsup>R (n - Suc 0)\<^esup>" and y = a in ring_tOp_commute, assumption+,
      simp add:ring_tOp_assoc,
      frule_tac x = "a^\<^bsup>R (n - Suc 0)\<^esup>" and y = b in ring_tOp_closed, assumption+)
 apply blast
done

lemma (in Idomain) idom_mult_cancel_r:"\<lbrakk>a \<in> carrier R;
       b \<in> carrier R; c \<in> carrier R; c \<noteq> \<zero>; a \<cdot>\<^sub>r c = b \<cdot>\<^sub>r c\<rbrakk> \<Longrightarrow> a = b"
apply (cut_tac ring_is_ag)
 apply (frule ring_tOp_closed[of "a" "c"], assumption+,
        frule ring_tOp_closed[of "b" "c"], assumption+)
 apply (simp add:aGroup.ag_eq_diffzero[of "R" "a \<cdot>\<^sub>r c" "b \<cdot>\<^sub>r c"],
        simp add:ring_inv1_1,
        frule aGroup.ag_mOp_closed[of "R" "b"], assumption,
        simp add:ring_distrib2[THEN sym, of "c" "a" "-\<^sub>a b"])
 apply (frule aGroup.ag_pOp_closed[of "R" "a" "-\<^sub>a b"], assumption+)
 apply (subst aGroup.ag_eq_diffzero[of R a b], assumption+)
 apply (rule contrapos_pp, simp+)
 apply (frule idom_tOp_nonzeros[of "a \<plusminus> -\<^sub>a b" c], assumption+, simp)
done

lemma (in Idomain) idom_mult_cancel_l:"\<lbrakk>a \<in> carrier R;
      b \<in> carrier R; c \<in> carrier R; c \<noteq> \<zero>; c \<cdot>\<^sub>r a = c \<cdot>\<^sub>r b\<rbrakk> \<Longrightarrow> a = b"
apply (simp add:ring_tOp_commute)
apply (simp add:idom_mult_cancel_r)
done

lemma (in Corps) invf_closed1:"x \<in> carrier K - {\<zero>} \<Longrightarrow>
                               invf K x \<in> (carrier K) - {\<zero>}"
apply (frule  invf_inv[of x], erule conjE)
 apply (rule contrapos_pp, simp+)
 apply (cut_tac f_is_ring) apply (
        simp add:Ring.ring_times_0_x[of K])
 apply (frule sym, thin_tac "\<zero> = 1\<^sub>r", simp, erule conjE)
 apply (frule Ring.ring_l_one[of K x], assumption)
 apply (rotate_tac -1, frule sym, thin_tac "1\<^sub>r \<cdot>\<^sub>r x = x",
        simp add:Ring.ring_times_0_x)
done

lemma (in Corps) linvf:"x \<in> carrier K - {\<zero>} \<Longrightarrow> (invf K x) \<cdot>\<^sub>r x = 1\<^sub>r"
by (simp add:invf_inv)

lemma (in Corps) field_is_ring:"Ring K"
by (simp add:f_is_ring)

lemma (in Corps) invf_one:"1\<^sub>r \<noteq> \<zero>  \<Longrightarrow> invf K (1\<^sub>r) = 1\<^sub>r"
apply (cut_tac field_is_ring)
 apply (frule_tac Ring.ring_one)
 apply (cut_tac invf_closed1 [of "1\<^sub>r"])
 apply (cut_tac linvf[of "1\<^sub>r"])
 apply (simp add:Ring.ring_r_one[of "K"])
 apply simp+
done

lemma (in Corps) field_tOp_assoc:"\<lbrakk>x \<in> carrier K; y \<in> carrier K; z \<in> carrier K\<rbrakk>
                                \<Longrightarrow> x \<cdot>\<^sub>r y \<cdot>\<^sub>r z =  x \<cdot>\<^sub>r (y \<cdot>\<^sub>r z)"
apply (cut_tac field_is_ring)
apply (simp add:Ring.ring_tOp_assoc)
done

lemma (in Corps) field_tOp_commute:"\<lbrakk>x \<in> carrier K; y \<in> carrier K\<rbrakk>
                                \<Longrightarrow> x \<cdot>\<^sub>r y  =  y \<cdot>\<^sub>r x"
apply (cut_tac field_is_ring)
apply (simp add:Ring.ring_tOp_commute)
done

lemma (in Corps) field_inv_inv:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> (x\<^bsup>\<hyphen>K\<^esup>)\<^bsup>\<hyphen>K\<^esup> = x"
apply (cut_tac invf_closed1[of "x"])
 apply (cut_tac invf_inv[of "x\<^bsup>\<hyphen>K\<^esup>"], erule conjE)
 apply (frule field_tOp_assoc[THEN sym, of "x\<^bsup>\<hyphen> K\<^esup>\<^bsup>\<hyphen> K\<^esup>" "x\<^bsup>\<hyphen> K\<^esup>" "x"],
        simp, assumption, simp)
 apply (cut_tac field_is_ring,
        simp add:Ring.ring_l_one Ring.ring_r_one, erule conjE,
        cut_tac invf_inv[of x], erule conjE, simp add:Ring.ring_r_one)
 apply simp+
done

lemma (in Corps) field_is_idom:"Idomain K"
apply (rule Idomain.intro)
 apply (simp add:field_is_ring)
 apply (cut_tac field_is_ring)
 apply (rule Idomain_axioms.intro)
 apply (rule contrapos_pp, simp+, erule conjE)
 apply (cut_tac x = a in invf_closed1, simp, simp, erule conjE)
 apply (frule_tac x = "a\<^bsup>\<hyphen> K\<^esup>" and y = a and z = b in field_tOp_assoc,
         assumption+)
 apply (simp add:linvf Ring.ring_times_x_0 Ring.ring_l_one)
done

lemma (in Corps) field_potent_nonzero:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                                       x^\<^bsup>K n\<^esup> \<noteq> \<zero>"
apply (cut_tac field_is_idom)
apply (cut_tac field_is_ring,
       simp add:Idomain.idom_potent_nonzero)
done

lemma (in Corps) field_potent_nonzero1:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> x\<^bsub>K\<^esub>\<^bsup>n\<^esup>  \<noteq> \<zero>"
apply (simp add:npowf_def)
apply (case_tac "0 \<le> n")
apply (simp add:field_potent_nonzero)

apply simp
 apply (cut_tac invf_closed1[of "x"], simp+, (erule conjE)+)
 apply (simp add:field_potent_nonzero)
 apply simp
done

lemma (in Corps) field_nilp_zero:"\<lbrakk>x \<in> carrier K; x^\<^bsup>K n\<^esup> = \<zero>\<rbrakk> \<Longrightarrow> x = \<zero>"
by (rule contrapos_pp, simp+, simp add:field_potent_nonzero)

lemma (in Corps) npowf_mem:"\<lbrakk>a \<in> carrier K; a \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                                    npowf K a n \<in> carrier K"
apply (simp add:npowf_def)
apply (cut_tac field_is_ring)
apply (case_tac "0 \<le> n", simp,
       simp add:Ring.npClose, simp)

apply (cut_tac invf_closed1[of "a"], simp, erule conjE,
       simp add:Ring.npClose, simp)
done

lemma (in Corps) field_npowf_exp_zero:"\<lbrakk>a \<in> carrier K; a \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                                    npowf K a 0 = 1\<^sub>r"
by (cut_tac field_is_ring, simp add:npowf_def)

lemma (in Corps) npow_exp_minusTr1:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; 0 \<le> i\<rbrakk>  \<Longrightarrow>
       0 \<le> i - (int j) \<longrightarrow>  x\<^bsub>K\<^esub>\<^bsup>(i - (int j))\<^esup> = x^\<^bsup>K (nat i)\<^esup> \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)^\<^bsup>K j\<^esup>"
apply (cut_tac field_is_ring,
       cut_tac invf_closed1[of "x"], simp,
       simp add:npowf_def, erule conjE)
apply (induct_tac "j", simp)
 apply (frule Ring.npClose[of "K" "x" "nat i"], assumption+,
        simp add:Ring.ring_r_one)
apply (rule impI, simp)
 apply (subst zdiff)
 apply (simp add:add.commute[of "1"])
 apply (cut_tac z = i and w = "int n + 1" in zdiff,
       simp only:minus_add_distrib,
       thin_tac "i - (int n + 1) = i + (- int n + - 1)")
 apply (cut_tac z = "i + - int n" in nat_diff_distrib[of "1"],
         simp, simp)
 apply (simp only:zdiff[of _ "1"], simp)

apply (cut_tac field_is_idom)
apply (frule_tac n = "nat i" in Ring.npClose[of "K" "x"], assumption+,
       frule_tac n = "nat i" in Ring.npClose[of "K" "x\<^bsup>\<hyphen> K\<^esup>"], assumption+,
       frule_tac n = n in Ring.npClose[of "K" "x\<^bsup>\<hyphen> K\<^esup>"], assumption+ )
apply (rule_tac a = "x^\<^bsup>K (nat (i + (- int n - 1)))\<^esup>" and
       b = "x^\<^bsup>K (nat i)\<^esup> \<cdot>\<^sub>r (x\<^bsup>\<hyphen> K\<^esup>^\<^bsup>K n\<^esup> \<cdot>\<^sub>r x\<^bsup>\<hyphen> K\<^esup>)" and c = x in
       Idomain.idom_mult_cancel_r[of "K"], assumption+)
 apply (simp add:Ring.npClose, rule Ring.ring_tOp_closed, assumption+,
        rule Ring.ring_tOp_closed, assumption+)
 apply (subgoal_tac "0 < nat (i - int n)")
 apply (subst Ring.npMulElmR, assumption+, simp,
        simp add:field_tOp_assoc[THEN sym, of "x^\<^bsup>K (nat i)\<^esup>" _ "x\<^bsup>\<hyphen> K\<^esup>"])
 apply (subst field_tOp_assoc[of _ _ x])
 apply (rule Ring.ring_tOp_closed[of K], assumption+)
 apply (simp add: linvf)
 apply (subst Ring.ring_r_one[of K], assumption)
 apply auto
 apply (metis Ring.npClose)
 apply (simp only: uminus_add_conv_diff [symmetric] add.assoc [symmetric])
 apply (simp add: algebra_simps nat_diff_distrib Suc_diff_Suc)
 apply (smt Ring.npMulElmR Suc_nat_eq_nat_zadd1 nat_diff_distrib' nat_int of_nat_0_le_iff)
done

lemma (in Corps) npow_exp_minusTr2:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; 0 \<le> i; 0 \<le> j;
                 0 \<le> i - j\<rbrakk>  \<Longrightarrow>  x\<^bsub>K\<^esub>\<^bsup>(i - j)\<^esup> = x^\<^bsup>K (nat i)\<^esup> \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)^\<^bsup>K (nat j)\<^esup>"
apply (frule npow_exp_minusTr1[of "x" "i" "nat j"], assumption+)
apply simp
done

lemma (in Corps) npowf_inv:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; 0 \<le> j\<rbrakk> \<Longrightarrow> x\<^bsub>K\<^esub>\<^bsup>j\<^esup> = (x\<^bsup>\<hyphen>K\<^esup>)\<^bsub>K\<^esub>\<^bsup>(-j)\<^esup>"
apply (simp add:npowf_def)
 apply (rule impI, simp add:zle)
 apply (simp add:field_inv_inv)
done

lemma (in Corps) npowf_inv1:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; \<not> 0 \<le> j\<rbrakk> \<Longrightarrow>
                                      x\<^bsub>K\<^esub>\<^bsup>j\<^esup> = (x\<^bsup>\<hyphen>K\<^esup>)\<^bsub>K\<^esub>\<^bsup>(-j)\<^esup>"
apply (simp add:npowf_def)
done

lemma (in Corps) npowf_inverse:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> x\<^bsub>K\<^esub>\<^bsup>j\<^esup> = (x\<^bsup>\<hyphen>K\<^esup>)\<^bsub>K\<^esub>\<^bsup>(-j)\<^esup>"
apply (case_tac "0 \<le> j")
apply (simp add:npowf_inv, simp add:npowf_inv1)
done

lemma (in Corps) npowf_expTr1:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; 0 \<le> i; 0 \<le> j;
                 0 \<le> i - j\<rbrakk> \<Longrightarrow> x\<^bsub>K\<^esub>\<^bsup>(i - j)\<^esup> = x\<^bsub>K\<^esub>\<^bsup>i\<^esup> \<cdot>\<^sub>r x\<^bsub>K\<^esub>\<^bsup>(- j)\<^esup>"
apply (simp add:npow_exp_minusTr2)
apply (simp add:npowf_def)
done

lemma (in Corps) npowf_expTr2:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; 0 \<le> i + j\<rbrakk> \<Longrightarrow>
                          x\<^bsub>K\<^esub>\<^bsup>(i + j)\<^esup> = x\<^bsub>K\<^esub>\<^bsup>i\<^esup> \<cdot>\<^sub>r x\<^bsub>K\<^esub>\<^bsup>j\<^esup>"
apply (cut_tac field_is_ring)
 apply (case_tac "0 \<le> i")
  apply (case_tac "0 \<le> j")
  apply (simp add:npowf_def, simp add:nat_add_distrib,
         rule Ring.npMulDistr[THEN sym], assumption+)
 apply (subst zminus_minus[THEN sym, of "i" "j"],
        subst npow_exp_minusTr2[of "x" "i" "-j"], assumption+)
  apply (simp add:zle, simp add:zless_imp_zle, simp add:npowf_def)
 apply (simp add:add.commute[of "i" "j"],
        subst zminus_minus[THEN sym, of "j" "i"],
        subst npow_exp_minusTr2[of "x" "j" "-i"], assumption+)
  apply (simp add:zle, simp add:zless_imp_zle, simp)
  apply (frule npowf_mem[of "x" "i"], assumption+,
         frule npowf_mem[of "x" "j"], assumption+,
         simp add:field_tOp_commute[of "x\<^bsub>K\<^esub>\<^bsup>i\<^esup>" "x\<^bsub>K\<^esub>\<^bsup>j\<^esup>"])
  apply (simp add:npowf_def)
done

lemma (in Corps) npowf_exp_add:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                          x\<^bsub>K\<^esub>\<^bsup>(i + j)\<^esup> = x\<^bsub>K\<^esub>\<^bsup>i\<^esup> \<cdot>\<^sub>r x\<^bsub>K\<^esub>\<^bsup>j\<^esup>"
apply (case_tac "0 \<le> i + j")
apply (simp add:npowf_expTr2)
apply (simp add:npowf_inv1[of "x" "i + j"])
 apply (simp add:zle)
apply (subgoal_tac "0 < -i + -j") prefer 2 apply simp
 apply (thin_tac "i + j < 0")
 apply (frule zless_imp_zle[of "0" "-i + -j"])
 apply (thin_tac "0 < -i + -j")
apply (cut_tac invf_closed1[of "x"])
apply (simp, erule conjE,
       frule npowf_expTr2[of "x\<^bsup>\<hyphen>K\<^esup>" "-i" "-j"], assumption+)
 apply (simp add:zdiff[THEN sym])
apply (simp add:npowf_inverse, simp)
done

lemma (in Corps) npowf_exp_1_add:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                                        x\<^bsub>K\<^esub>\<^bsup>(1 + j)\<^esup> = x \<cdot>\<^sub>r x\<^bsub>K\<^esub>\<^bsup>j\<^esup>"
apply (simp add:npowf_exp_add[of "x" "1" "j"])
apply (cut_tac field_is_ring)
apply (simp add:npowf_def, simp add:Ring.ring_l_one)
done

lemma (in Corps) npowf_minus:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> (x\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup> = x\<^bsub>K\<^esub>\<^bsup>(- j)\<^esup>"
apply (frule npowf_exp_add[of "x" "j" "-j"], assumption+)
 apply (simp add:field_npowf_exp_zero)
apply (cut_tac field_is_ring)
apply (frule npowf_mem[of "x" "j"], assumption+)
 apply (frule field_potent_nonzero1[of "x" "j"], assumption+)
apply (cut_tac invf_closed1[of "x\<^bsub>K\<^esub>\<^bsup>j\<^esup>"], simp, erule conjE,
       frule Ring.ring_r_one[of "K" "(x\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>"], assumption, simp,
      thin_tac "1\<^sub>r = x\<^bsub>K\<^esub>\<^bsup>j\<^esup> \<cdot>\<^sub>r x\<^bsub>K\<^esub>\<^bsup>- j\<^esup>",
      frule npowf_mem[of "x" "-j"], assumption+)
apply (simp add:field_tOp_assoc[THEN sym], simp add:linvf,
       simp add:Ring.ring_l_one, simp)
done

lemma (in Ring) residue_fieldTr:"\<lbrakk>maximal_ideal R mx; x \<in> carrier(qring R mx);
 x \<noteq> \<zero>\<^bsub>(qring R mx)\<^esub>\<rbrakk> \<Longrightarrow>\<exists>y\<in>carrier (qring R mx). y \<cdot>\<^sub>r\<^bsub>(qring R mx)\<^esub> x = 1\<^sub>r\<^bsub>(qring R mx)\<^esub>"
apply (frule maximal_ideal_ideal[of "mx"])
apply (simp add:qring_carrier)
 apply (simp add:qring_zero)
 apply (simp add:qring_def)
 apply (erule bexE)
 apply (frule sym, thin_tac "a \<uplus>\<^bsub>R\<^esub> mx = x", simp)
 apply (frule_tac a = a in ar_coset_same4_1[of "mx"], assumption+)
 apply (frule_tac x = a in maximal_prime_Tr0[of "mx"], assumption+)
 apply (cut_tac ring_one)
 apply (rotate_tac -2, frule sym, thin_tac "mx \<minusplus> R \<diamondsuit>\<^sub>p a = carrier R")
 apply (frule_tac B = "mx \<minusplus> R \<diamondsuit>\<^sub>p a" in eq_set_inc[of "1\<^sub>r" "carrier R"],
                  assumption+,
        thin_tac "carrier R = mx \<minusplus> R \<diamondsuit>\<^sub>p a")
 apply (frule ideal_subset1[of mx])
 apply (frule_tac a = a in principal_ideal,
        frule_tac I = "R \<diamondsuit>\<^sub>p a" in ideal_subset1)
 apply (cut_tac ring_is_ag,
        simp add:aGroup.set_sum, (erule bexE)+)
 apply (thin_tac "ideal R (R \<diamondsuit>\<^sub>p a)", thin_tac "R \<diamondsuit>\<^sub>p a \<subseteq> carrier R",
        simp add:Rxa_def, (erule bexE)+, simp, thin_tac "k = r \<cdot>\<^sub>r a")
 apply (frule_tac a = r and b = a in rcostOp[of "mx"], assumption+)
 apply (frule_tac x = r and y = a in ring_tOp_closed, assumption+)
 apply (frule_tac a = "r \<cdot>\<^sub>r a" and x = h and b = "1\<^sub>r" in
        aGroup.ag_eq_sol2[of "R"], assumption+)
       apply (simp add:ideal_subset) apply (simp add:ring_one, simp)
       apply (frule_tac a = h and b = "1\<^sub>r \<plusminus> -\<^sub>a (r \<cdot>\<^sub>r a)" and A = mx in
              eq_elem_in, assumption+)
 apply (frule_tac a = "r \<cdot>\<^sub>r a" and b = "1\<^sub>r" in ar_coset_same1[of "mx"],
        rule ring_tOp_closed, assumption+, rule ring_one, assumption)
  apply (frule_tac a1 = "r \<cdot>\<^sub>r a" and h1 = h in aGroup.arcos_fixed[THEN sym,
         of R mx],  unfold ideal_def, erule conjE, assumption+,
         thin_tac "R +> mx \<and> (\<forall>r\<in>carrier R. \<forall>x\<in>mx. r \<cdot>\<^sub>r x \<in> mx)",
         thin_tac "x = a \<uplus>\<^bsub>R\<^esub> mx",
         thin_tac "1\<^sub>r = h \<plusminus> r \<cdot>\<^sub>r a",
         thin_tac "h = 1\<^sub>r \<plusminus> -\<^sub>a (r \<cdot>\<^sub>r a)", thin_tac "1\<^sub>r \<plusminus> -\<^sub>a (r \<cdot>\<^sub>r a) \<in> mx")
  apply (rename_tac b h k r) apply simp
  apply blast
done

(*
constdefs (structure R)
 field_cd::"_ \<Rightarrow> bool"
 "field_cd R  == \<forall>x\<in>(carrier R - {\<zero>}). \<exists>y\<in>carrier R.
                                                y \<cdot>\<^sub>r x = 1\<^sub>r" *)
(* field condition  *) (*
constdefs (structure R)
 rIf :: "_ \<Rightarrow> 'a  \<Rightarrow> 'a " *) (** rIf is ring_invf **) (*
 "rIf R == \<lambda>x. (SOME y. y \<in> carrier R \<and> y \<cdot>\<^sub>r x = 1\<^sub>r)"
*) (*
constdefs (structure R)
  Rf::"_ \<Rightarrow> 'a field"
  "Rf R == \<lparr>carrier = carrier R, pop = pop R, mop = mop R, zero = zero R,
               tp = tp R, un = un R, invf = rIf R\<rparr>" *)

(*
constdefs (structure R)
 Rf ::  "_ \<Rightarrow> \<lparr> carrier :: 'a set,
  pOp :: ['a, 'a] \<Rightarrow> 'a, mOp ::'a \<Rightarrow> 'a, zero :: 'a, tOp :: ['a, 'a] \<Rightarrow> 'a,
  one ::'a, iOp ::'a \<Rightarrow> 'a\<rparr>"

  "Rf R  == \<lparr> carrier = carrier R, pOp = pOp R, mOp = mOp R, zero = zero R,
  tOp = tOp R, one = one R, iOp = ring_iOp R\<rparr>" *)
(*
lemma (in Ring) rIf_mem:"\<lbrakk>field_cd R; x \<in> carrier R - {\<zero>}\<rbrakk> \<Longrightarrow>
                     rIf R x \<in> carrier R \<and> rIf R x \<noteq> \<zero>"
apply (simp add:rIf_def)
apply (rule someI2_ex)
apply (simp add:field_cd_def, blast)
apply (simp add:field_cd_def)
 apply (thin_tac "\<forall>x\<in>carrier R - {\<zero>}. \<exists>y\<in>carrier R. y \<cdot>\<^sub>r x = 1\<^sub>r")
 apply (erule conjE)+
 apply (rule contrapos_pp, simp+)
 apply (frule sym, thin_tac "\<zero> \<cdot>\<^sub>r x = 1\<^sub>r", simp add:ring_times_0_x)
  apply (frule ring_l_one[of "x"])
 apply (simp add:ring_times_0_x)
done

lemma (in Ring) rIf:"\<lbrakk>field_cd R; x \<in> carrier R - {\<zero>}\<rbrakk> \<Longrightarrow>
                                           (rIf R x) \<cdot>\<^sub>r x = 1\<^sub>r"
apply (simp add:rIf_def)
apply (rule someI2_ex)
apply (simp add:field_cd_def, blast)
apply simp
done

lemma (in Ring) field_cd_integral:"field_cd R \<Longrightarrow> Idomain R"
apply (rule Idomain.intro)
 apply assumption
 apply (rule Idomain_axioms.intro)

apply (rule contrapos_pp, simp+, erule conjE)
apply (cut_tac x = a in rIf_mem, assumption, simp, erule conjE)
apply (frule_tac x = "rIf R a" and y = a and z = b in ring_tOp_assoc,
                 assumption+, simp add:rIf)
apply (simp add:ring_l_one ring_times_x_0)
done

lemma (in Ring) Rf_field:"field_cd R \<Longrightarrow> field (Rf R)"
apply (rule field.intro)
 apply (simp add:Rf_def)
 apply (rule Ring.intro)
 apply (simp add:pop_closed)
 apply ( cut_tac ring_is_ag, simp add:aGroup.ag_pOp_assoc)
 apply (simp add:Rf_def,
         cut_tac ring_is_ag, simp add:aGroup.ag_pOp_commute)
 apply (simp add:mop_closed)
 apply (simp add:


apply (rule conjI)
 prefer 2
 apply (rule conjI)
 apply (rule univar_func_test, rule ballI)
 apply (simp, erule conjE, simp add:Rf_def)
 apply (rule rIf_mem, assumption+, simp)
apply (rule allI, rule impI)
 apply (simp add:Rf_def)
 apply (frule_tac x = x in rIf, simp, assumption)

 apply (subst Rf_def, simp add:Ring_def)
 apply (cut_tac ring_is_ag)
 apply (rule conjI, simp add:aGroup_def)
 apply (rule conjI, (rule allI, rule impI)+, simp add:aGroup.ag_pOp_assoc)
 apply (rule conjI, (rule allI, rule impI)+, simp add:aGroup.ag_pOp_commute)
 apply (rule conjI, rule univar_func_test, rule ballI,
                                              simp add:aGroup.ag_mOp_closed)
 apply (rule conjI, rule allI, rule impI, simp add:aGroup.ag_l_inv1)
 apply (simp add:aGroup.ag_inc_zero)
 apply (rule conjI, rule allI, rule impI, simp add:aGroup.ag_l_zero)

 apply (rule conjI, rule bivar_func_test, (rule ballI)+,
                                          simp add:ring_tOp_closed)
 apply (rule conjI, (rule allI, rule impI)+, simp add:ring_tOp_assoc)
 apply (rule conjI, (rule allI, rule impI)+, simp add:ring_tOp_commute)
 apply (simp add:ring_one)
 apply (rule conjI, (rule allI, rule impI)+, simp add:ring_distrib1)
 apply (rule allI, rule impI, simp add:ring_l_one)
done
 *)

lemma (in Ring) residue_field_cd:"maximal_ideal R mx \<Longrightarrow>
                                           Corps (qring R mx)"
apply (rule Corps.intro)
apply (rule Ring.qring_ring, rule Ring_axioms)
apply (simp add:maximal_ideal_ideal)
apply (simp add:residue_fieldTr[of "mx"])
done

(*
lemma (in Ring) qRf_field:"maximal_ideal R mx \<Longrightarrow> field (Rf (qring R mx))"
apply (frule maximal_ideal_ideal[of "mx"])
apply (frule qring_ring [of "mx"])
 apply (frule residue_field_cd[of "mx"])
 apply (rule Ring.Rf_field, assumption+)
done

lemma (in Ring) qRf_pj_rHom:"maximal_ideal R mx \<Longrightarrow>
                          (pj R mx) \<in> rHom R (Rf (qring R mx))"
apply (frule maximal_ideal_ideal[of "mx"])
apply (frule pj_Hom[OF Ring, of "mx"])
apply (simp add:rHom_def aHom_def Rf_def)
done *)

lemma (in Ring) maximal_set_idealTr:
       "maximal_set {I. ideal R I \<and> S \<inter> I = {}} mx \<Longrightarrow> ideal R mx"
by (simp add:maximal_set_def)

lemma (in Ring) maximal_setTr:"\<lbrakk>maximal_set {I. ideal R I \<and> S \<inter> I = {}} mx;
                                         ideal R J; mx \<subset> J \<rbrakk> \<Longrightarrow> S \<inter> J \<noteq> {}"
by (rule contrapos_pp, simp+, simp add:psubset_eq, erule conjE,
       simp add:maximal_set_def, blast)

lemma (in Ring) mulDisj:"\<lbrakk>mul_closed_set R S; 1\<^sub>r \<in> S; \<zero> \<notin> S;
    T = {I. ideal R I \<and> S \<inter> I = {}}; maximal_set T mx \<rbrakk> \<Longrightarrow> prime_ideal R mx"
apply (simp add:prime_ideal_def)
apply (rule conjI, simp add:maximal_set_def,
       rule conjI, simp add:maximal_set_def)
apply (rule contrapos_pp, simp+)
apply ((erule conjE)+, blast)

apply ((rule ballI)+, rule impI)
apply (rule contrapos_pp, simp+, (erule conjE)+)
apply (cut_tac a = x in id_ideal_psub_sum[of "mx"],
               simp add:maximal_set_def, assumption+,
       cut_tac a = y in id_ideal_psub_sum[of "mx"],
               simp add:maximal_set_def, assumption+)
apply (frule_tac J = "mx \<minusplus> R \<diamondsuit>\<^sub>p x" in maximal_setTr[of "S" "mx"],
       rule sum_ideals, simp add:maximal_set_def,
       simp add:principal_ideal, assumption,
       thin_tac "mx \<subset> mx \<minusplus> R \<diamondsuit>\<^sub>p x")
apply (frule_tac J = "mx \<minusplus> R \<diamondsuit>\<^sub>p y" in maximal_setTr[of "S" "mx"],
       rule sum_ideals, simp add:maximal_set_def,
       simp add:principal_ideal, assumption,
       thin_tac "mx \<subset> mx \<minusplus> R \<diamondsuit>\<^sub>p y")
apply (frule_tac A = "S \<inter> (mx \<minusplus> R \<diamondsuit>\<^sub>p x)" in nonempty_ex,
       frule_tac A = "S \<inter> (mx \<minusplus> R \<diamondsuit>\<^sub>p y)" in nonempty_ex,
       (erule exE)+, simp, (erule conjE)+)
apply (rename_tac x y s1 s2,
       thin_tac "S \<inter> (mx \<minusplus> R \<diamondsuit>\<^sub>p x) \<noteq> {}",
       thin_tac "S \<inter> (mx \<minusplus> R \<diamondsuit>\<^sub>p y) \<noteq> {}")
apply (frule maximal_set_idealTr,
       frule_tac a = x in principal_ideal,
       frule_tac a = y in principal_ideal,
       frule ideal_subset1[of mx],
       frule_tac I = "R \<diamondsuit>\<^sub>p x" in ideal_subset1,
       frule_tac I = "R \<diamondsuit>\<^sub>p y" in ideal_subset1)
apply (cut_tac ring_is_ag,
       simp add:aGroup.set_sum[of R mx],
       erule bexE, erule bexE, simp)
apply (frule_tac s = s1 and t = s2 in mul_closed_set_tOp_closed, simp,
       assumption, simp,
       frule_tac c = h in subsetD[of mx "carrier R"], assumption+,
       frule_tac c = k and A = "R \<diamondsuit>\<^sub>p x" in subsetD[of _ "carrier R"],
       assumption+)
apply (
       cut_tac mul_closed_set_sub,
       frule_tac c = s2 in subsetD[of S "carrier R"], assumption+,
       simp add:ring_distrib2)
apply ((erule bexE)+, simp,
       frule_tac c = ha in subsetD[of mx "carrier R"], assumption+,
       frule_tac c = ka and A = "R \<diamondsuit>\<^sub>p y" in subsetD[of _ "carrier R"],
       assumption+,
       simp add:ring_distrib1)
apply (frule_tac x = h and r = ha in ideal_ring_multiple1[of mx], assumption+)
apply (frule_tac x = h and r = ka in ideal_ring_multiple1[of mx], assumption+,
       frule_tac x = ha and r = k in ideal_ring_multiple[of mx], assumption+)
apply (frule_tac a = x and b = y and x = k and y = ka in
                  mul_two_principal_idealsTr, assumption+,
       erule bexE,
       frule_tac x = "x \<cdot>\<^sub>r y" and r = r in ideal_ring_multiple[of mx],
       assumption+,
       rotate_tac -2, frule sym, thin_tac "k \<cdot>\<^sub>r ka = r \<cdot>\<^sub>r (x \<cdot>\<^sub>r y)", simp)
 apply (frule_tac x = "h \<cdot>\<^sub>r ha \<plusminus> h \<cdot>\<^sub>r ka" and y = "k \<cdot>\<^sub>r ha \<plusminus> k \<cdot>\<^sub>r ka" in
        ideal_pOp_closed[of mx])
 apply (rule ideal_pOp_closed, assumption+)+
 apply (simp add:maximal_set_def)
 apply blast
 apply assumption
done

lemma (in Ring) ex_mulDisj_maximal:"\<lbrakk>mul_closed_set R S; \<zero> \<notin> S; 1\<^sub>r \<in> S;
       T = {I. ideal R I \<and> S \<inter> I = {}}\<rbrakk> \<Longrightarrow>  \<exists>mx. maximal_set T mx"
apply (cut_tac A="{ I. ideal R I \<and> S \<inter> I = {}}" in Zorn_Lemma2)
prefer 2
  apply (simp add:maximal_set_def)

apply (rule ballI)
apply (case_tac "C = {}")
 apply (cut_tac zero_ideal, blast)

apply (subgoal_tac "C \<in> chains {I. ideal R I \<and> I \<subset> carrier R}")
apply (frule chains_un, assumption)
 apply (subgoal_tac "S \<inter> (\<Union> C) = {}")
 apply (subgoal_tac "\<forall>x\<in>C. x \<subseteq> \<Union> C",  blast)
apply (rule ballI, rule subsetI, simp add:CollectI)
 apply blast

apply (rule contrapos_pp, simp+)
 apply (frule_tac A = S and B = "\<Union> C" in nonempty_int)
 apply (erule exE)
 apply (simp, erule conjE, erule bexE)
 apply (simp add:chains_def, erule conjE)
 apply (frule_tac c = X and A = C and B = "{I. ideal R I \<and> S \<inter> I = {}}" in
        subsetD, assumption+,
        thin_tac "C \<subseteq> {I. ideal R I \<and> I \<subset> carrier R}",
        thin_tac "C \<subseteq> {I. ideal R I \<and> S \<inter> I = {}}")
 apply (simp, blast)

apply (simp add:chains_def chain_subset_def, erule conjE)
 apply (rule subsetI)
 apply (frule_tac c = x and A = C and B = "{I. ideal R I \<and> S \<inter> I = {}}" in
                  subsetD, assumption+,
        thin_tac "C \<subseteq> {I. ideal R I \<and> S \<inter> I = {}}",
        thin_tac "T = {I. ideal R I \<and> S \<inter> I = {}}")
 apply (simp, thin_tac "\<forall>x\<in>C. \<forall>y\<in>C. x \<subseteq> y \<or> y \<subseteq> x", erule conjE)
 apply (simp add:psubset_eq ideal_subset1)
 apply (rule contrapos_pp, simp+)
 apply (rotate_tac -1, frule sym, thin_tac "x = carrier R",
        thin_tac "carrier R = x")
 apply (cut_tac ring_one, blast)
done

lemma (in Ring) ex_mulDisj_prime:"\<lbrakk>mul_closed_set R S; \<zero> \<notin> S; 1\<^sub>r \<in> S\<rbrakk> \<Longrightarrow>
                            \<exists>mx. prime_ideal R mx \<and> S \<inter> mx = {}"
apply (frule ex_mulDisj_maximal[of "S" "{I. ideal R I \<and> S \<inter> I = {}}"],
               assumption+, simp, erule exE)
 apply (frule_tac mx = mx in mulDisj [of "S" "{I. ideal R I \<and> S \<inter> I = {}}"],
                  assumption+, simp, assumption)
 apply (simp add:maximal_set_def, (erule conjE)+, blast)
done

lemma (in Ring) nilradTr1:"\<not> zeroring R \<Longrightarrow> nilrad R = \<Inter> {p. prime_ideal R p}"
apply (rule equalityI)
 (* nilrad R \<subseteq> \<Inter>Collect (prime_ideal R) *)
apply (rule subsetI)
 apply (simp add:nilrad_def CollectI nilpotent_def)
 apply (erule conjE, erule exE)
 apply (rule allI, rule impI)
 apply (frule_tac prime_ideal_ideal)
 apply (frule sym, thin_tac "x^\<^bsup>R n\<^esup> = \<zero>", frule ideal_zero, simp)
 apply (case_tac "n = 0", simp)
 apply (frule Zero_ring1[THEN not_sym], simp)
 apply (rule_tac P = xa and x = x in npow_in_prime,assumption+, blast)

apply (rule subsetI)
 apply (rule contrapos_pp, simp+)
 apply (frule id_maximal_Exist, erule exE,
        frule maximal_prime)
 apply (frule_tac a = I in forall_spec, assumption,
        frule_tac I = I in prime_ideal_ideal,
        frule_tac h = x and I = I in ideal_subset, assumption)
apply (subgoal_tac "\<zero> \<notin> {s. \<exists>n. s = npow R x n} \<and>
                                  1\<^sub>r \<in> {s. \<exists>n. s = npow R x n}")
apply (subgoal_tac "mul_closed_set R {s. \<exists>n. s = npow R x n}")
apply (erule conjE)
apply (frule_tac S = "{s. \<exists>n. s = npow R x n}" in ex_mulDisj_prime,
       assumption+, erule exE, erule conjE)
apply (subgoal_tac "x \<in> {s. \<exists>n. s = x^\<^bsup>R n\<^esup>}", blast)

apply simp
apply (cut_tac t = x in np_1[THEN sym], assumption, blast)

apply (thin_tac "\<zero> \<notin> {s. \<exists>n. s = x^\<^bsup>R n\<^esup>} \<and> 1\<^sub>r \<in> {s. \<exists>n. s = x^\<^bsup>R n\<^esup>}",
       thin_tac "\<forall>xa. prime_ideal R xa \<longrightarrow> x \<in> xa")
apply (subst mul_closed_set_def)
 apply (rule conjI)
 apply (rule subsetI, simp, erule exE)
 apply (simp add:npClose)
apply ((rule ballI)+, simp, (erule exE)+, simp)
 apply (simp add:npMulDistr, blast)

apply (rule conjI)
 apply simp
 apply (rule contrapos_pp, simp+, erule exE)
 apply (frule sym, thin_tac "\<zero> = x^\<^bsup>R n\<^esup>")
 apply (simp add:nilrad_def nilpotent_def)

apply simp
 apply (cut_tac x1 = x in npow_0[THEN sym, of "R"], blast)
done

lemma (in Ring) nonilp_residue_nilrad:"\<lbrakk>\<not> zeroring R; x \<in> carrier R;
        nilpotent (qring R (nilrad R)) (x \<uplus>\<^bsub>R\<^esub> (nilrad R))\<rbrakk> \<Longrightarrow>
                   x \<uplus>\<^bsub>R\<^esub> (nilrad R) = \<zero>\<^bsub>(qring R (nilrad R))\<^esub>"
apply (simp add:nilpotent_def)
 apply (erule exE)
 apply (cut_tac id_nilrad_ideal)
 apply (simp add:qring_zero)
 apply (cut_tac "Ring")
 apply (simp add:npQring)
 apply (frule_tac x = x and n = n in npClose)
 apply (frule_tac I = "nilrad R" and a = "x^\<^bsup>R n\<^esup>" in ar_coset_same3,
             assumption+)
 apply (rule_tac I = "nilrad R" and a = x in ar_coset_same4, assumption)
 apply (thin_tac "x^\<^bsup>R n\<^esup> \<uplus>\<^bsub>R\<^esub> nilrad R = nilrad R",
        simp add:nilrad_def nilpotent_def, erule exE)
 apply (simp add:npMulExp, blast)
done

lemma (in Ring) ex_contid_maximal:"\<lbrakk> S = {1\<^sub>r}; \<zero> \<notin> S; ideal R I; I \<inter> S = {};
T = {J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}\<rbrakk> \<Longrightarrow> \<exists>mx. maximal_set T mx"
apply (cut_tac A="{J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}" in Zorn_Lemma2)
apply (rule ballI)
apply (case_tac "C = {}") (** case C = {} **)
 apply blast             (** case C = {} done **)
     (** existence of sup in C **)
apply (subgoal_tac "\<Union>C\<in>{J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J} \<and>
                                         (\<forall>x\<in>C. x \<subseteq>  \<Union>C)")
 apply blast
apply (rule conjI,
       simp add:CollectI)
apply (subgoal_tac "C \<in> chains {I. ideal R I \<and> I \<subset> carrier R}")
apply (rule conjI,
       simp add:chains_un)
apply (rule conjI)
apply (rule contrapos_pp, simp+, erule bexE)
 apply (thin_tac " C \<in> chains {I. ideal R I \<and> I \<subset> carrier R}")
 apply (simp add:chains_def, erule conjE)
 apply (frule_tac c = x and A = C and B = "{J. ideal R J \<and> 1\<^sub>r \<notin> J \<and> I \<subseteq> J}"
         in subsetD, assumption+, simp,
        thin_tac "C \<in> chains {I. ideal R I \<and> I \<subset> carrier R}")
 apply (frule_tac A = C in nonempty_ex, erule exE, simp add:chains_def,
        erule conjE,
        frule_tac c = x and A = C and B = "{J. ideal R J \<and> 1\<^sub>r \<notin> J \<and> I \<subseteq> J}" in
                  subsetD, assumption+, simp, (erule conjE)+)
 apply (rule_tac A = I and B = x and C = "\<Union>C" in subset_trans, assumption,
        rule_tac B = x and A = C in Union_upper, assumption+)
 apply (simp add:chains_def, erule conjE)
 apply (rule subsetI, simp)
 apply (frule_tac c = x and A = C and B = "{J. ideal R J \<and> 1\<^sub>r \<notin> J \<and> I \<subseteq> J}"
        in subsetD, assumption+, simp, (erule conjE)+)
 apply (subst psubset_eq, simp add:ideal_subset1)
 apply (rule contrapos_pp, simp+, simp add:ring_one)

 apply (rule ballI)
 apply (rule Union_upper, assumption)
 apply (erule bexE)
 apply (simp add:maximal_set_def)
 apply blast
done

lemma (in Ring) contid_maximal:"\<lbrakk>S = {1\<^sub>r}; \<zero> \<notin> S; ideal R I; I \<inter> S = {};
             T = {J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}; maximal_set T mx\<rbrakk> \<Longrightarrow>
                                                maximal_ideal R mx"
apply (simp add:maximal_set_def maximal_ideal_def)
apply (erule conjE)+
apply (rule equalityI)
  (** {J. ideal R J \<and> mx \<subseteq> J} \<subseteq> {mx, carrier R} **)
  apply (rule subsetI, simp add:CollectI, erule conjE)
 apply (case_tac "x = mx", simp, simp)
 apply (subgoal_tac "1\<^sub>r \<in> x")
 apply (rule_tac  I = x in ideal_inc_one, assumption+)
 apply (rule contrapos_pp, simp+)
apply (drule spec[of _ mx])
 apply (simp add:whole_ideal,
        rule subsetI, rule ideal_subset[of "mx"], assumption+)
done

lemma (in Ring) ideal_contained_maxid:"\<lbrakk>\<not>(zeroring R); ideal R I; 1\<^sub>r \<notin> I\<rbrakk> \<Longrightarrow>
                    \<exists>mx. maximal_ideal R mx \<and> I \<subseteq> mx"
apply (cut_tac ex_contid_maximal[of "{1\<^sub>r}" "I"
                      "{J. ideal R J \<and> {1\<^sub>r} \<inter> J = {} \<and> I \<subseteq> J}"])
apply (erule exE,
       cut_tac mx = mx in contid_maximal[of "{1\<^sub>r}" "I"
                         "{J. ideal R J \<and> {1\<^sub>r} \<inter> J = {} \<and> I \<subseteq> J}"])
apply simp
 apply (frule Zero_ring1, simp,
        assumption, simp, simp, simp,
        simp add:maximal_set_def, (erule conjE)+, blast,
        simp, frule Zero_ring1, simp)
 apply (assumption, simp, simp)
done

lemma (in Ring) nonunit_principal_id:"\<lbrakk>a \<in> carrier R; \<not> (Unit R a)\<rbrakk> \<Longrightarrow>
                                             (R \<diamondsuit>\<^sub>p a) \<noteq> (carrier R)"
apply (rule contrapos_pp, simp+)
apply (frule sym, thin_tac "R \<diamondsuit>\<^sub>p a = carrier R")
apply (cut_tac ring_one)
 apply (frule eq_set_inc[of "1\<^sub>r" "carrier R" "R \<diamondsuit>\<^sub>p a"], assumption,
        thin_tac "carrier R = R \<diamondsuit>\<^sub>p a", thin_tac "1\<^sub>r \<in> carrier R")
apply (simp add:Rxa_def, erule bexE, simp add:ring_tOp_commute[of _ "a"],
       frule sym, thin_tac "1\<^sub>r = a \<cdot>\<^sub>r r")
apply (simp add:Unit_def)
done

lemma (in Ring) nonunit_contained_maxid:"\<lbrakk>\<not>(zeroring R); a \<in> carrier R;
                \<not> Unit R a \<rbrakk>  \<Longrightarrow>  \<exists>mx. maximal_ideal R mx \<and> a \<in>  mx"
apply (frule principal_ideal[of "a"],
       frule ideal_contained_maxid[of "R \<diamondsuit>\<^sub>p a"], assumption)
 apply (rule contrapos_pp, simp+,
        frule ideal_inc_one[of "R \<diamondsuit>\<^sub>p a"], assumption,
        simp add:nonunit_principal_id)
apply (erule exE, erule conjE)
 apply (frule a_in_principal[of "a"])
 apply (frule_tac B = mx in subsetD[of "R \<diamondsuit>\<^sub>p a" _ "a"], assumption, blast)
done

definition
  local_ring :: "_ \<Rightarrow> bool" where
  "local_ring R == Ring R \<and> \<not> zeroring R \<and> card {mx. maximal_ideal R mx} = 1"

lemma (in Ring) local_ring_diff:"\<lbrakk>\<not> zeroring R; ideal R mx; mx \<noteq> carrier R;
  \<forall>a\<in> (carrier R - mx). Unit R a \<rbrakk> \<Longrightarrow> local_ring R \<and> maximal_ideal R mx"
apply (subgoal_tac "{mx} = {m. maximal_ideal R m}")
 apply (cut_tac singletonI[of "mx"], simp)
 apply (frule sym, thin_tac "{mx} = {m. maximal_ideal R m}")
 apply (simp add:local_ring_def, simp add:Ring)
apply (rule equalityI)
 apply (rule subsetI, simp)
 apply (simp add:maximal_ideal_def)
 apply (simp add:ideal_inc_one1[of "mx", THEN sym])
 apply (thin_tac "x = mx", simp)
 apply (rule equalityI)
  apply (rule subsetI, simp, erule conjE)
  apply (case_tac "x \<noteq> mx")
  apply (frule_tac A = x and B = mx in sets_not_eq, assumption)
  apply (erule bexE)
  apply (frule_tac h = a and I = x in ideal_subset, assumption+)
  apply (frule_tac x = a in bspec, simp)
  apply (frule_tac I = x and a = a in ideal_inc_unit1, assumption+,
        simp)
  apply simp

  apply (rule subsetI, simp)
  apply (erule disjE)
  apply simp
  apply (simp add:whole_ideal ideal_subset1)

apply (rule subsetI)
 apply simp
 apply (subgoal_tac "x \<subseteq> mx",
        thin_tac "\<forall>a\<in>carrier R - mx. Unit R a",
        simp add:maximal_ideal_def, (erule conjE)+)
 apply (subgoal_tac "mx \<in> {J. ideal R J \<and> x \<subseteq> J}", simp)
 apply (thin_tac "{J. ideal R J \<and> x \<subseteq> J} = {x, carrier R}")
 apply simp

 apply (rule contrapos_pp, simp+)
 apply (simp add:subset_eq, erule bexE)
 apply (frule_tac mx = x in maximal_ideal_ideal,
        frule_tac x = xa in bspec,
        thin_tac "\<forall>a\<in>carrier R - mx. Unit R a", simp,
        simp add:ideal_subset)
 apply (frule_tac I = x and a = xa in ideal_inc_unit, assumption+,
                  simp add:maximal_ideal_def)
done

lemma (in Ring) localring_unit:"\<lbrakk>\<not> zeroring R; maximal_ideal R mx;
                \<forall>x. x \<in> mx \<longrightarrow> Unit R (x \<plusminus> 1\<^sub>r) \<rbrakk> \<Longrightarrow> local_ring R"
apply (frule maximal_ideal_ideal[of "mx"])
apply (frule local_ring_diff[of "mx"], assumption)
 apply (simp add:maximal_ideal_def, erule conjE)
 apply (simp add:ideal_inc_one1[THEN sym, of "mx"])
 apply (rule ballI, simp, erule conjE)

 apply (frule_tac x = a in maximal_prime_Tr0[of "mx"], assumption+)

 apply (frule sym, thin_tac "mx \<minusplus> R \<diamondsuit>\<^sub>p a = carrier R",
        cut_tac ring_one,
        frule_tac a = "1\<^sub>r" and A = "carrier R" and B = "mx \<minusplus> R \<diamondsuit>\<^sub>p a" in
                  eq_set_inc, assumption+,
        thin_tac "carrier R = mx \<minusplus> R \<diamondsuit>\<^sub>p a")
 apply (frule_tac a = a in principal_ideal,
       frule ideal_subset1[of mx],
       frule_tac I = "R \<diamondsuit>\<^sub>p a" in ideal_subset1)
 apply (cut_tac ring_is_ag,
        simp add:aGroup.set_sum, (erule bexE)+)
 apply (simp add:Rxa_def, erule bexE, simp)
 apply (frule sym, thin_tac "1\<^sub>r = h \<plusminus> r \<cdot>\<^sub>r a",
        frule_tac x = r and y = a in ring_tOp_closed, assumption+,
        frule_tac h = h in ideal_subset[of "mx"], assumption+)
 apply (frule_tac I = mx and x = h in ideal_inv1_closed, assumption)
 apply (frule_tac a = "-\<^sub>a h" in forall_spec, assumption,
        thin_tac "\<forall>x. x \<in> mx \<longrightarrow> Unit R (x \<plusminus> (h \<plusminus> r \<cdot>\<^sub>r a))",
        thin_tac "h \<plusminus> r \<cdot>\<^sub>r a = 1\<^sub>r")
 apply (frule_tac h = "-\<^sub>a h" in ideal_subset[of "mx"], assumption,
        frule_tac x1 = "-\<^sub>a h" and y1 = h and z1 = "r \<cdot>\<^sub>r a" in
        aGroup.ag_pOp_assoc[THEN sym], assumption+,
        simp add:aGroup.ag_l_inv1 aGroup.ag_l_zero,
        thin_tac "k = r \<cdot>\<^sub>r a", thin_tac "h \<plusminus> r \<cdot>\<^sub>r a \<in> carrier R",
        thin_tac "h \<in> carrier R", thin_tac "-\<^sub>a h \<in> mx",
        thin_tac "-\<^sub>a h \<plusminus> (h \<plusminus> r \<cdot>\<^sub>r a) = r \<cdot>\<^sub>r a")
 apply (simp add:ring_tOp_commute, simp add:Unit_def, erule bexE,
        simp add:ring_tOp_assoc,
        frule_tac x = r and y = b in ring_tOp_closed, assumption+, blast)
 apply simp
done

definition
  J_rad ::"_ \<Rightarrow> 'a set" where
  "J_rad R = (if (zeroring R) then (carrier R) else
                 \<Inter> {mx. maximal_ideal R mx})"
  (** if zeroring R then \<Inter> {mx. maximal_ideal R mx} is UNIV, hence
      we restrict UNIV to carrier R **)

lemma (in Ring) zeroring_J_rad_empty:"zeroring R \<Longrightarrow> J_rad R = carrier R"
by (simp add:J_rad_def)

lemma (in Ring) J_rad_mem:"x \<in> J_rad R \<Longrightarrow> x \<in> carrier R"
apply (simp add:J_rad_def)
apply (case_tac "zeroring R", simp)
apply simp
apply (frule id_maximal_Exist, erule exE)
 apply (frule_tac a = I in forall_spec, assumption,
        thin_tac "\<forall>xa. maximal_ideal R xa \<longrightarrow> x \<in> xa")
 apply (frule maximal_ideal_ideal,
        simp add:ideal_subset)
done

lemma (in Ring) J_rad_unit:"\<lbrakk>\<not> zeroring R; x \<in> J_rad R\<rbrakk> \<Longrightarrow>
            \<forall>y. (y\<in> carrier R \<longrightarrow> Unit R (1\<^sub>r \<plusminus> (-\<^sub>a x) \<cdot>\<^sub>r y))"
apply (cut_tac ring_is_ag,
       rule allI, rule impI,
       rule contrapos_pp, simp+)
apply (frule J_rad_mem[of "x"],
       frule_tac x = x and y = y in ring_tOp_closed, assumption,
       frule_tac x = "x \<cdot>\<^sub>r y" in aGroup.ag_mOp_closed, assumption+)
apply (cut_tac ring_one,
      frule_tac x = "1\<^sub>r" and y = "-\<^sub>a (x \<cdot>\<^sub>r y)" in aGroup.ag_pOp_closed,
      assumption+)
 apply (frule_tac a = "1\<^sub>r \<plusminus> -\<^sub>a (x \<cdot>\<^sub>r y)" in nonunit_contained_maxid,
        assumption+, simp add:ring_inv1_1)
apply (erule exE, erule conjE)
 apply (simp add:J_rad_def,
        frule_tac a = mx in forall_spec, assumption,
        thin_tac "\<forall>xa. maximal_ideal R xa \<longrightarrow> x \<in> xa",
        frule_tac mx = mx in maximal_ideal_ideal,
        frule_tac I = mx and x = x and r = y in ideal_ring_multiple1,
        assumption+)
 apply (frule_tac I = mx and x = "x \<cdot>\<^sub>r y" in ideal_inv1_closed,
           assumption+)

 apply (frule_tac I = mx and a = "1\<^sub>r" and b = "-\<^sub>a (x \<cdot>\<^sub>r y)" in ideal_ele_sumTr2,
        assumption+)
 apply (simp add:maximal_ideal_def)
done

end
