(**        Algebra7  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            h_koba@math.cst.nihon-u.ac.jp
                            May 3, 2004.
                            April 6, 2007 (revised)

   chapter 5. Modules
    section 3.   a module over two rings 
    section 4.   eSum and Generators
     subsection 4-1. sum up coefficients
     subsection 4-2. free generators 
   **)

theory Algebra7 imports Algebra6 begin

chapter "Modules"

section "Basic properties of Modules"

record ('a, 'b) Module = "'a aGroup" +
  sprod  :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>s\<index>" 76)

locale Module = aGroup M for M (structure) +
  fixes R (structure)
  assumes  sc_Ring: "Ring R" 
  and  sprod_closed :
      "\<lbrakk> a \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>s m \<in> carrier M" 
    and sprod_l_distr:
      "\<lbrakk>a \<in> carrier R; b \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow>
       (a \<plusminus>\<^bsub>R\<^esub> b) \<cdot>\<^sub>s m = a \<cdot>\<^sub>s m \<plusminus>\<^bsub>M\<^esub> b \<cdot>\<^sub>s m" 
    and sprod_r_distr:
      "\<lbrakk> a \<in> carrier R; m \<in> carrier M; n \<in> carrier M \<rbrakk> \<Longrightarrow>
      a \<cdot>\<^sub>s (m \<plusminus>\<^bsub>M\<^esub> n) = a \<cdot>\<^sub>s m \<plusminus>\<^bsub>M\<^esub> a \<cdot>\<^sub>s n"
    and sprod_assoc:
      "\<lbrakk> a \<in> carrier R; b \<in> carrier R; m \<in> carrier M \<rbrakk> \<Longrightarrow>
      (a \<cdot>\<^sub>r\<^bsub>R\<^esub> b) \<cdot>\<^sub>s m = a \<cdot>\<^sub>s (b \<cdot>\<^sub>s m)"  
    and sprod_one:
      "m \<in> carrier M \<Longrightarrow> (1\<^sub>r\<^bsub>R\<^esub>) \<cdot>\<^sub>s m = m" 

definition 
  submodule :: "[('b, 'm) Ring_scheme, ('a, 'b, 'c) Module_scheme, 'a set] \<Rightarrow>
            bool" where
  "submodule R A H \<longleftrightarrow> H \<subseteq> carrier A \<and> A +> H \<and> (\<forall>a. \<forall>m. 
                     (a \<in> carrier R \<and> m \<in> H) \<longrightarrow> (sprod A a m) \<in> H)"

definition
  mdl :: "[('a, 'b, 'm) Module_scheme, 'a set] \<Rightarrow> ('a, 'b) Module" where
  "mdl M H = \<lparr>carrier = H, pop = pop M, mop = mop M, zero = zero M,
    sprod = \<lambda>a. \<lambda>x\<in>H. sprod M a x\<rparr>" 

abbreviation
  MODULE  (infixl "module" 58) where
 "R module M == Module M R"
 

lemma (in Module) module_is_ag: "aGroup M" ..

lemma (in Module) module_inc_zero:" \<zero>\<^bsub>M\<^esub> \<in> carrier M"
apply (simp add:ag_inc_zero) (** type of M is ('c, 'a, 'd) Module_scheme **)
done                         (** type of M is (?'b, ?'b, ?'z) Module_scheme **)

lemma (in Module) submodule_subset:"submodule R M H \<Longrightarrow> H \<subseteq> carrier M"
apply (simp add:submodule_def)
done

lemma (in Module) submodule_asubg:"submodule R M H \<Longrightarrow> M +> H"
by (simp add:submodule_def)

lemma (in Module) submodule_subset1:"\<lbrakk>submodule R M H; h \<in> H\<rbrakk> \<Longrightarrow>
                            h \<in> carrier M"
apply (simp add:submodule_def)
apply (erule conjE)+
apply (simp add:subsetD)
done

lemma (in Module) submodule_inc_0:"submodule R M H \<Longrightarrow>
                                           \<zero>\<^bsub>M\<^esub> \<in> H" 
apply (simp add:submodule_def, (erule conjE)+)
apply (rule asubg_inc_zero, assumption+)
done

lemma (in Module) sc_un:" m \<in> carrier M \<Longrightarrow> 1\<^sub>r\<^bsub>R\<^esub> \<cdot>\<^sub>s m = m"
apply (simp add:sprod_one)
done

lemma (in Module) sc_mem:"\<lbrakk>a \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow>
           a \<cdot>\<^sub>s m \<in> carrier M"
apply (simp add:sprod_closed)
done

lemma (in Module) submodule_sc_closed:"\<lbrakk>submodule R M H; 
 a \<in> carrier R; h \<in> H\<rbrakk> \<Longrightarrow>  a \<cdot>\<^sub>s h \<in> H"
apply (simp add:submodule_def)
done

lemma (in Module) sc_assoc:"\<lbrakk>a \<in> carrier R; b \<in> carrier R; 
 m \<in> carrier M\<rbrakk> \<Longrightarrow> (a \<cdot>\<^sub>r\<^bsub>R\<^esub> b) \<cdot>\<^sub>s m =  a \<cdot>\<^sub>s ( b \<cdot>\<^sub>s m)"
apply (simp add:sprod_assoc)
done

lemma (in Module) sc_l_distr:"\<lbrakk>a \<in> carrier R; b \<in> carrier R; 
 m \<in> carrier M\<rbrakk> \<Longrightarrow> (a \<plusminus>\<^bsub>R\<^esub> b)\<cdot>\<^sub>s m = a \<cdot>\<^sub>s m \<plusminus>  b \<cdot>\<^sub>s m"
apply (simp add:sprod_l_distr)
done

lemma (in Module) sc_r_distr:"\<lbrakk>a \<in> carrier R; m \<in> carrier M; n \<in> carrier M\<rbrakk> \<Longrightarrow>
                 a \<cdot>\<^sub>s (m \<plusminus> n) = a \<cdot>\<^sub>s m \<plusminus>  a \<cdot>\<^sub>s n"
apply (simp add:sprod_r_distr)
done

lemma (in Module) sc_0_m:"m \<in> carrier M \<Longrightarrow> \<zero>\<^bsub>R\<^esub>\<cdot>\<^sub>s m = \<zero>\<^bsub>M\<^esub>"
apply (cut_tac sc_Ring,
       frule Ring.ring_is_ag,
       frule aGroup.ag_inc_zero [of "R"],
       frule sc_l_distr[of "\<zero>\<^bsub>R\<^esub>" "\<zero>\<^bsub>R\<^esub>" "m"], assumption+,
       frule sc_mem [of "\<zero>\<^bsub>R\<^esub>" m], assumption+)
apply (simp add:aGroup.ag_l_zero, frule sym,
       thin_tac "\<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m = \<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m \<plusminus> \<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m")
apply (frule ag_eq_sol1 [of "\<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m" "\<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m" "\<zero>\<^bsub>R\<^esub> \<cdot>\<^sub>s m"], assumption+,   
       simp add:ag_l_inv1)
done

lemma (in Module) sc_a_0:"a \<in> carrier R \<Longrightarrow> a \<cdot>\<^sub>s \<zero>  = \<zero>"
apply (cut_tac ag_inc_zero,
       frule sc_r_distr[of a \<zero> \<zero>], assumption+,
       frule sc_mem [of a \<zero>], assumption+)
apply (simp add:ag_l_zero, frule sym,
       thin_tac "a \<cdot>\<^sub>s \<zero> = a \<cdot>\<^sub>s \<zero> \<plusminus> a \<cdot>\<^sub>s \<zero>")
apply (frule ag_eq_sol1 [of "a \<cdot>\<^sub>s \<zero>" "a \<cdot>\<^sub>s \<zero>" "a \<cdot>\<^sub>s \<zero>"], assumption+,   
       simp add:ag_l_inv1)
done

lemma (in Module) sc_minus_am:"\<lbrakk>a \<in> carrier R; m \<in> carrier M\<rbrakk>
                     \<Longrightarrow> -\<^sub>a (a \<cdot>\<^sub>s m) = a \<cdot>\<^sub>s (-\<^sub>a m)"
apply (frule ag_mOp_closed [of m],
       frule sc_r_distr[of a m "-\<^sub>a m"], assumption+,
       simp add:ag_r_inv1,
       simp add:sc_a_0, frule sym,
       thin_tac "\<zero> = a \<cdot>\<^sub>s m \<plusminus> a \<cdot>\<^sub>s (-\<^sub>a m)")
 apply (frule sc_mem [of a m], assumption+,
        frule sc_mem [of a "-\<^sub>a m"], assumption+,
        frule ag_eq_sol1 [of "a \<cdot>\<^sub>s m" "a \<cdot>\<^sub>s (-\<^sub>a m)" "\<zero>"], assumption+,
        simp add:ag_inc_zero, assumption)
 apply (frule ag_mOp_closed [of "a \<cdot>\<^sub>s m"],
        simp add:ag_r_zero)
done

lemma (in Module) sc_minus_am1:"\<lbrakk>a \<in> carrier R; m \<in> carrier M\<rbrakk>
            \<Longrightarrow> -\<^sub>a (a \<cdot>\<^sub>s m) = (-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s m"
apply (cut_tac sc_Ring, frule Ring.ring_is_ag,
       frule aGroup.ag_mOp_closed [of R a], assumption+,
       frule sc_l_distr[of a "-\<^sub>a\<^bsub>R\<^esub> a" m], assumption+,
       simp add:aGroup.ag_r_inv1 [of "R"],
       simp add:sc_0_m, frule sym) apply (
       thin_tac "\<zero> = a \<cdot>\<^sub>s m \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s m")
 apply (frule sc_mem [of a m], assumption+,
        frule sc_mem [of "-\<^sub>a\<^bsub>R\<^esub> a" m], assumption+)
 apply (frule ag_eq_sol1 [of "a \<cdot>\<^sub>s m" "(-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s m" \<zero>], assumption+,
        simp add:ag_inc_zero, assumption)
 apply (frule ag_mOp_closed [of "a \<cdot>\<^sub>s m"])
 apply (thin_tac "a \<cdot>\<^sub>s m \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s m = \<zero>",
        simp add:ag_r_zero)
done

lemma (in Module) submodule_0:"submodule R M {\<zero>}" 
apply (simp add:submodule_def)
apply (simp add:ag_inc_zero)
apply (simp add:asubg_zero)
apply (rule allI, rule impI)
apply (simp add:sc_a_0)
done   

lemma (in Module) submodule_whole:"submodule R M (carrier M)" 
apply (simp add:submodule_def)
apply (simp add:asubg_whole)
apply ((rule allI)+, rule impI, erule conjE)
apply (simp add:sc_mem)
done

lemma (in Module) submodule_pOp_closed:"\<lbrakk>submodule R M H; h \<in> H; k \<in> H\<rbrakk> \<Longrightarrow> 
                  h \<plusminus> k \<in> H"
apply (simp add:submodule_def)
apply (erule conjE)+
apply (thin_tac "\<forall>a m. a \<in> carrier R \<and> m \<in> H \<longrightarrow> a \<cdot>\<^sub>s m \<in> H")
apply (simp add:asubg_pOp_closed)
done

lemma (in Module) submodule_mOp_closed:"\<lbrakk>submodule R M H; h \<in> H\<rbrakk>
                 \<Longrightarrow> -\<^sub>a h \<in> H"
apply (simp add:submodule_def,
       (erule conjE)+,
       thin_tac "\<forall>a m. a \<in> carrier R \<and> m \<in> H \<longrightarrow> a \<cdot>\<^sub>s m \<in> H")
apply (rule asubg_mOp_closed, assumption+)
done 

definition
  mHom :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
                    ('c, 'b, 'm2) Module_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) set"
        (*  ("(3HOM\<^sub>_/ _/ _)" [90, 90, 91]90 ) *) where
  "mHom R M N = {f. f \<in> aHom M N \<and> 
             (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. f (a \<cdot>\<^sub>s\<^bsub>M\<^esub> m) = a \<cdot>\<^sub>s\<^bsub>N\<^esub> (f m))}"

definition
  mimg :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
           ('c, 'b, 'm2) Module_scheme, 'a \<Rightarrow> 'c] \<Rightarrow>  ('c, 'b) Module" 
                 ("(4mimg\<^bsub>_ _,_\<^esub>/ _)" [88,88,88,89]88) where
  "mimg\<^bsub>R M,N\<^esub> f = mdl N (f ` (carrier M))"

definition
  mzeromap :: "[('a, 'b, 'm1) Module_scheme, ('c, 'b, 'm2) Module_scheme]
                              \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "mzeromap M N = (\<lambda>x\<in>carrier M. \<zero>\<^bsub>N\<^esub>)"

lemma (in Ring) mHom_func:"f \<in> mHom R M N \<Longrightarrow> f \<in> carrier M \<rightarrow> carrier N"
by (simp add:mHom_def aHom_def)

lemma (in Module) mHom_test:"\<lbrakk>R module N; f \<in> carrier M \<rightarrow> carrier N \<and> 
      f \<in> extensional (carrier M) \<and> 
     (\<forall>m\<in>carrier M. \<forall>n\<in>carrier M. f (m \<plusminus>\<^bsub>M\<^esub> n) = f m \<plusminus>\<^bsub>N\<^esub> (f n)) \<and> 
     (\<forall>a\<in>carrier R. \<forall>m\<in>carrier M. f (a \<cdot>\<^sub>s\<^bsub>M\<^esub> m) = a \<cdot>\<^sub>s\<^bsub>N\<^esub> (f m))\<rbrakk> \<Longrightarrow>
     f \<in> mHom R M N"  
apply (simp add:mHom_def)
apply (simp add:aHom_def)
done

lemma (in Module) mHom_mem:"\<lbrakk>R module N; f \<in> mHom R M N; m \<in> carrier M\<rbrakk>
 \<Longrightarrow> f m \<in> carrier N"
apply (simp add:mHom_def aHom_def) apply (erule conjE)+
apply (simp add:Pi_def)
done

lemma (in Module) mHom_add:"\<lbrakk>R module N; f \<in> mHom R M N; m \<in> carrier M; 
             n \<in> carrier M\<rbrakk> \<Longrightarrow> f (m \<plusminus> n) = f m \<plusminus>\<^bsub>N\<^esub> (f n)"
apply (simp add:mHom_def) apply (erule conjE)+
apply (frule Module.module_is_ag [of N R],
       cut_tac module_is_ag)
apply (simp add:aHom_add)
done 
 
lemma (in Module) mHom_0:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow> f (\<zero>) = \<zero>\<^bsub>N\<^esub>"
apply (simp add:mHom_def, (erule conjE)+,
       frule Module.module_is_ag [of N],
       cut_tac module_is_ag)
apply (simp add:aHom_0_0)
done

lemma (in Module) mHom_inv:"\<lbrakk>R module N; m \<in> carrier M; f \<in> mHom R M N\<rbrakk> \<Longrightarrow> 
                 f (-\<^sub>a m) = -\<^sub>a\<^bsub>N\<^esub> (f m)"
apply (cut_tac module_is_ag,
       frule Module.module_is_ag [of N])
apply (simp add:mHom_def, (erule conjE)+)
apply (rule aHom_inv_inv, assumption+)
done

lemma (in Module) mHom_lin:"\<lbrakk>R module N; m \<in> carrier M; f \<in> mHom R M N;
                    a \<in> carrier R\<rbrakk> \<Longrightarrow> f (a \<cdot>\<^sub>s m) = a \<cdot>\<^sub>s\<^bsub>N\<^esub> (f m)"
apply (simp add:mHom_def)
done

lemma (in Module) mker_inc_zero:
           "\<lbrakk>R module N; f \<in> mHom R M N \<rbrakk> \<Longrightarrow> \<zero> \<in> (ker\<^bsub>M,N\<^esub> f)" 
apply (simp add:ker_def) 
apply (simp add:module_inc_zero)
apply (simp add:mHom_0)
done

lemma (in Module) mHom_eq_ker:"\<lbrakk>R module N; f \<in> mHom R M N; a \<in> carrier M; 
      b\<in> carrier M; a \<plusminus> (-\<^sub>a b) \<in> ker\<^bsub>M,N\<^esub> f\<rbrakk> \<Longrightarrow> f a = f b"
apply (simp add:ker_def, erule conjE)
apply (cut_tac module_is_ag,
       frule aGroup.ag_mOp_closed [of "M" "b"], assumption+,
       simp add:mHom_add, simp add:mHom_inv,
       thin_tac "aGroup M")
apply (frule mHom_mem [of N f a], assumption+,
       frule mHom_mem [of N f b], assumption+,
       frule Module.module_is_ag[of N]) 
apply (subst aGroup.ag_eq_diffzero[of N], assumption+)
done  

lemma (in Module) mHom_ker_eq:"\<lbrakk>R module N; f \<in> mHom R M N; a \<in> carrier M; 
      b\<in> carrier M; f a = f b\<rbrakk> \<Longrightarrow> a \<plusminus> (-\<^sub>a b) \<in> ker\<^bsub>M,N\<^esub> f"
apply (simp add:ker_def)
 apply (frule ag_mOp_closed[of b])
 apply (simp add:ag_pOp_closed)
 apply (simp add:mHom_add mHom_inv)
 apply (frule mHom_mem [of N f b], assumption+)
 apply (frule_tac R = R and M = N in Module.module_is_ag,
        simp add:aGroup.ag_r_inv1)
done
 
lemma (in Module) mker_submodule:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                                    submodule R M (ker\<^bsub>M,N\<^esub> f)"
apply (cut_tac module_is_ag,
       frule Module.module_is_ag [of N])
apply (simp add:submodule_def)
apply (rule conjI)
 apply (rule subsetI, simp add:ker_def)

apply (rule conjI)
 apply (simp add:mHom_def, (erule conjE)+, simp add:ker_subg)

apply ((rule allI)+, rule impI, erule conjE)
 apply (simp add:ker_def, erule conjE)
 apply (simp add:sc_mem)
 apply (subst mHom_lin [of N _ f], assumption+, simp) (* key *)
apply (simp add:Module.sc_a_0[of N])
done

lemma (in Module) mker_mzeromap:"R module N \<Longrightarrow>
                         ker\<^bsub>M,N\<^esub> (mzeromap M N) = carrier M"
apply (simp add:ker_def mzeromap_def)
done

lemma (in Module) mdl_carrier:"submodule R M H \<Longrightarrow> carrier (mdl M H) = H"
apply (simp add:mdl_def)
done 

lemma (in Module) mdl_is_ag:"submodule R M H \<Longrightarrow> aGroup (mdl M H)"
apply (cut_tac module_is_ag)
apply (rule aGroup.intro)
 apply (simp add:mdl_def)
 apply (clarsimp simp: submodule_def asubg_pOp_closed)

 apply (simp add:mdl_def)
 apply (simp add:submodule_def, (erule conjE)+,
        frule_tac c = a in subsetD[of H "carrier M"], assumption+,
        frule_tac c = b in subsetD[of H "carrier M"], assumption+,
        frule_tac c = c in subsetD[of H "carrier M"], assumption+,
        simp add:aGroup.ag_pOp_assoc)

 apply (simp add:submodule_def, (erule conjE)+,
        simp add:mdl_def,
        frule_tac c = a in subsetD[of H "carrier M"], assumption+,
        frule_tac c = b in subsetD[of H "carrier M"], assumption+,
        simp add:aGroup.ag_pOp_commute)

 apply (simp add:mdl_def)
 apply (simp add:submodule_def aGroup.asubg_mOp_closed)

 apply (simp add:mdl_def,
        simp add:submodule_def, (erule conjE)+,
        frule_tac c = a in subsetD[of H "carrier M"], assumption+,
        rule aGroup.ag_l_inv1, assumption+)         

 apply (simp add:mdl_def,
        simp add:submodule_def, (erule conjE)+,
        simp add:asubg_inc_zero)

 apply (simp add:mdl_def, simp add:submodule_def, (erule conjE)+,
        frule_tac c = a in subsetD[of H "carrier M"], assumption+)
 apply (simp add:ag_l_zero)
done

lemma (in Module) mdl_is_module:"submodule R M H \<Longrightarrow> R module (mdl M H)" 
apply (rule Module.intro)
apply (simp add:mdl_is_ag)

apply (rule Module_axioms.intro)
apply (simp add:sc_Ring)

apply (simp add:mdl_def)
 apply (simp add:submodule_def) 

apply (simp add:mdl_def)
 apply (simp add:submodule_def, (erule conjE)+,
        frule_tac c = m in subsetD[of H "carrier M"], assumption+,
        simp add:sc_l_distr)

apply (simp add:mdl_def submodule_def, (erule conjE)+,
       simp add:asubg_pOp_closed,
       frule_tac c = m in subsetD[of H "carrier M"], assumption+,
       frule_tac c = n in subsetD[of H "carrier M"], assumption+,
       simp add:sc_r_distr)
apply (simp add:mdl_def submodule_def, (erule conjE)+,
       frule_tac c = m in subsetD[of H "carrier M"], assumption+,
       simp add:sc_assoc)
apply (simp add:mdl_def submodule_def, (erule conjE)+,
       frule_tac c = m in subsetD[of H "carrier M"], assumption+,
       simp add:sprod_one)
done   

lemma (in Module) submodule_of_mdl:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk>
                   \<Longrightarrow> submodule R (mdl M N) H"
apply (subst submodule_def)
 apply (rule conjI, simp add:mdl_def)
 apply (rule conjI)
 apply (rule aGroup.asubg_test[of "mdl M N" H])
 apply (frule mdl_is_module[of N],
        simp add:Module.module_is_ag, simp add:mdl_def)
 apply (simp add:submodule_def[of R M H], (erule conjE)+)
 apply (frule asubg_inc_zero[of H], simp add:nonempty)

 apply ((rule ballI)+, simp add:mdl_def)
 apply (simp add:submodule_def[of R M H], (erule conjE)+)
 apply (frule_tac x = b in asubg_mOp_closed[of H], assumption+)
 apply (rule asubg_pOp_closed[of H], assumption+)

apply ((rule allI)+, rule impI, erule conjE)
 apply (simp add:mdl_def subsetD)
 apply (simp add:submodule_def[of R M H])
done

lemma (in Module) img_set_submodule:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
         submodule R N (f ` (carrier M))"
apply (simp add:submodule_def)
apply (rule conjI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (erule bexE, simp, thin_tac "x = f xa")
  apply (simp add:mHom_mem)
apply (rule conjI)
 apply (frule Module.module_is_ag [of N])
 apply (rule aGroup.asubg_test, assumption+)
 apply (rule subsetI) apply (simp add:image_def)
 apply (erule bexE) apply (simp add:mHom_mem)
 apply (cut_tac ag_inc_zero,
        simp add:mHom_mem,  simp add:nonempty)
 apply ((rule ballI)+, simp add:image_def)
 apply ((erule bexE)+, simp)
 apply (simp add:mHom_inv[THEN sym],
        frule_tac x = xa in ag_mOp_closed,
        simp add:mHom_add[THEN sym, of N f],
        frule_tac x = "x" and y = "-\<^sub>a xa" in ag_pOp_closed, assumption+)
 apply blast

apply ((rule allI)+, rule impI, erule conjE)
 apply (simp add:image_def, erule bexE, simp)
 apply (simp add:mHom_lin[THEN sym, of N _ f])
 apply (frule_tac a = a and m = x in sc_mem, assumption) 
 apply blast 
done

lemma (in Module) mimg_module:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                                              R module (mimg R M N f)"
apply (simp add:mimg_def)
apply (rule Module.mdl_is_module[of N R "f ` (carrier M)"], assumption)
apply (simp add:img_set_submodule)
done
   
lemma (in Module) surjec_to_mimg:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                                       surjec\<^bsub>M, (mimg R M N f)\<^esub> f"
apply (simp add:surjec_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:mimg_def mdl_def)
 apply (rule conjI)
 apply (simp add:mHom_def aHom_def restrict_def extensional_def)
 apply ((rule ballI)+, simp add:mimg_def mdl_def, simp add:mHom_add)
apply (simp add:mimg_def mdl_def)
 apply (simp add:surj_to_def image_def)
done
 
definition
  tOp_mHom :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
    ('c, 'b, 'm2) Module_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "tOp_mHom R M N f g = (\<lambda>x \<in> carrier M. (f x \<plusminus>\<^bsub>N\<^esub> (g x)))"

definition
  iOp_mHom :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
    ('c, 'b, 'm2) Module_scheme] \<Rightarrow>  ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "iOp_mHom R M N f = (\<lambda>x \<in> carrier M. (-\<^sub>a\<^bsub>N\<^esub> (f x)))" 

definition
  sprod_mHom ::"[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
    ('c, 'b, 'm2) Module_scheme] \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "sprod_mHom R M N a f = (\<lambda>x \<in> carrier M. a \<cdot>\<^sub>s\<^bsub>N\<^esub> (f x))"

definition
  HOM :: "[('b, 'more) Ring_scheme, ('a, 'b, 'more1) Module_scheme, 
    ('c, 'b, 'more2) Module_scheme] \<Rightarrow> ('a \<Rightarrow> 'c, 'b) Module"   
    ("(3HOM\<^bsub>_\<^esub> _/ _)" [90, 90, 91] 90) where
 "HOM\<^bsub>R\<^esub> M N = \<lparr>carrier = mHom R M N, pop = tOp_mHom R M N, 
  mop = iOp_mHom R M N, zero = mzeromap M N,  sprod =sprod_mHom R M N \<rparr>"

lemma (in Module) zero_HOM:"R module N \<Longrightarrow>
         mzeromap M N = \<zero>\<^bsub>HOM\<^bsub>R\<^esub> M N\<^esub>"
apply (simp add:HOM_def)
done

lemma (in Module) tOp_mHom_closed:"\<lbrakk>R module N; f \<in> mHom R M N; g \<in> mHom R M N\<rbrakk>
      \<Longrightarrow> tOp_mHom R M N f g \<in> mHom R M N"
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = f and m = x in mHom_mem [of N], assumption+,
        frule_tac f = g and m = x in mHom_mem [of N], assumption+,
        frule Module.module_is_ag [of N], 
        simp add:aGroup.ag_pOp_closed[of N])
apply (rule conjI)
 apply (simp add:tOp_mHom_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:tOp_mHom_def)
 apply (simp add:ag_pOp_closed)
            
apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+,
       frule_tac f = f and m = n in mHom_mem [of N], assumption+,
       frule_tac f = g and m = m in mHom_mem [of N], assumption+,
       frule_tac f = g and m = n in mHom_mem [of N], assumption+,
       simp add:mHom_add,
       frule Module.module_is_ag [of N],
       subst aGroup.pOp_assocTr43[of "N"], assumption+,
       frule_tac x = "f n" and y = "g m" in aGroup.ag_pOp_commute [of "N"],
                                                              assumption+)
apply simp
apply (subst aGroup.pOp_assocTr43[of "N"], assumption+, simp) 

apply (rule ballI)+
apply (simp add:tOp_mHom_def) 
apply (frule_tac a = a and m = m in sc_mem, assumption, simp) 
apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+,
       frule_tac f = g and m = m in mHom_mem [of N], assumption+,
       frule_tac a = a and m = "f m" and n = "g m" in 
                                  Module.sc_r_distr[of N R], assumption+,
      simp)
apply (simp add:mHom_lin)
done

lemma (in Module) iOp_mHom_closed:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk>
                                     \<Longrightarrow> iOp_mHom R M N f \<in> mHom R M N"
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:iOp_mHom_def)
 apply (frule_tac f = f and m = x in mHom_mem [of N], assumption+)
 apply (frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_mOp_closed)
apply (rule conjI)
 apply (simp add:iOp_mHom_def restrict_def extensional_def)
apply (rule conjI) apply (rule ballI)+
 apply (simp add:iOp_mHom_def)
 apply (simp add:ag_pOp_closed)
 apply (simp add:mHom_add)
  apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+,
         frule_tac f = f and m = n in mHom_mem [of N], assumption+)
 apply (frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_p_inv)

apply (rule ballI)+
apply (simp add:iOp_mHom_def)
apply (simp add:sc_mem)
 apply (simp add:mHom_lin)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+)
 apply (simp add:Module.sc_minus_am[of N])
done

lemma (in Module) mHom_ex_zero:"R module N \<Longrightarrow>  mzeromap M N \<in> mHom R M N"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def,
        rule conjI,
        simp add:mzeromap_def, simp add:Module.module_inc_zero)

 apply (simp add:mzeromap_def extensional_def)

 apply ((rule ballI)+,
         simp add:ag_pOp_closed,
         frule Module.module_is_ag [of N],
         frule aGroup.ag_inc_zero [of "N"],
         simp add:aGroup.ag_l_zero)
apply ((rule ballI)+,
       simp add:mzeromap_def,
       simp add:sc_mem)
 apply (simp add:Module.sc_a_0)
done

lemma (in Module) mHom_eq:"\<lbrakk>R module N; f \<in> mHom R M N; g \<in> mHom R M N; 
                            \<forall>m\<in>carrier M. f m = g m\<rbrakk> \<Longrightarrow> f = g"  
apply (simp add:mHom_def aHom_def)
 apply (erule conjE)+
 apply (rule funcset_eq, assumption+)
done

lemma (in Module) mHom_l_zero:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk>
              \<Longrightarrow> tOp_mHom R M N (mzeromap M N) f = f"
apply (frule mHom_ex_zero [of N])
apply (frule tOp_mHom_closed [of N "mzeromap M N" f], assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:tOp_mHom_def, simp add:mzeromap_def)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+)
 apply (frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_l_zero[of N])
done

lemma  (in Module) mHom_l_inv:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk>
       \<Longrightarrow> tOp_mHom R M N (iOp_mHom R M N f) f = mzeromap M N"
apply (frule mHom_ex_zero [of N])
apply (frule_tac f = f in iOp_mHom_closed [of N], assumption,
       frule_tac f = "iOp_mHom R M N f" and g = f in tOp_mHom_closed [of N],
        assumption+,
       frule mHom_ex_zero [of N])
apply (rule mHom_eq, assumption+, rule ballI)
 apply (simp add:tOp_mHom_def iOp_mHom_def, simp add:mzeromap_def)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+)
 apply (frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_l_inv1)
done

lemma  (in Module) mHom_tOp_assoc:"\<lbrakk>R module N; f \<in> mHom R M N; g \<in> mHom R M N;
        h \<in> mHom R M N\<rbrakk> \<Longrightarrow> tOp_mHom R M N (tOp_mHom R M N f g) h =
          tOp_mHom R M N f (tOp_mHom R M N g h)"
apply (frule_tac f = f and g = g in tOp_mHom_closed [of N], assumption+,
       frule_tac f = "tOp_mHom R M N f g" and g = h in 
                      tOp_mHom_closed [of N], assumption+,
       frule_tac f = g and g = h in tOp_mHom_closed [of N], assumption+,
       frule_tac f = f and g = "tOp_mHom R M N g h" in 
                      tOp_mHom_closed [of N], assumption+) 
 apply (rule mHom_eq, assumption+, rule ballI,
        thin_tac "tOp_mHom R M N f g \<in> mHom R M N",
        thin_tac "tOp_mHom R M N (tOp_mHom R M N f g) h \<in> mHom R M N",
        thin_tac "tOp_mHom R M N g h \<in> mHom R M N",
        thin_tac "tOp_mHom R M N f (tOp_mHom R M N g h) \<in> mHom R M N")
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+,
        frule_tac f = g and m = m in mHom_mem [of N], assumption+,
        frule_tac f = h and m = m in mHom_mem [of N], assumption+)
apply (frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_pOp_assoc)
done

lemma (in Module) mHom_tOp_commute:"\<lbrakk>R module N; f \<in> mHom R M N; 
        g \<in> mHom R M N\<rbrakk> \<Longrightarrow> tOp_mHom R M N f g = tOp_mHom R M N g f"
apply (frule_tac f = f and g = g in tOp_mHom_closed [of N], assumption+,
       frule_tac f = g and g = f in tOp_mHom_closed [of N], assumption+)
apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (thin_tac "tOp_mHom R M N f g \<in> mHom R M N",
        thin_tac "tOp_mHom R M N g f \<in> mHom R M N")
 apply (simp add:tOp_mHom_def)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+,
        frule_tac f = g and m = m in mHom_mem [of N], assumption+,
        frule Module.module_is_ag [of N])
 apply (simp add:aGroup.ag_pOp_commute)
done

lemma  (in Module) HOM_is_ag:"R module N \<Longrightarrow> aGroup (HOM\<^bsub>R\<^esub> M N)"
apply (rule aGroup.intro)
 apply (simp add:HOM_def)
 apply (simp add:tOp_mHom_closed)

apply (simp add:HOM_def)
 apply (simp add:mHom_tOp_assoc)

apply (simp add:HOM_def)
 apply (simp add:mHom_tOp_commute)

apply (simp add:HOM_def)
 apply (simp add:iOp_mHom_closed)

apply (simp add:HOM_def,
       simp add:mHom_l_inv)

apply (simp add:HOM_def)
 apply (simp add:mHom_ex_zero)

apply (simp add:HOM_def,
       simp add:mHom_l_zero)
done

lemma (in Module) sprod_mHom_closed:"\<lbrakk>R module N; a \<in> carrier R; 
       f \<in> mHom R M N\<rbrakk> \<Longrightarrow> sprod_mHom R M N a f \<in> mHom R M N"
apply (rule mHom_test, assumption+)
apply (rule conjI)
 apply (simp add:Pi_def)
 apply (rule allI, rule impI, simp add:sprod_mHom_def,
        frule_tac f = f and m = x in mHom_mem [of N], assumption+,
        simp add:Module.sc_mem [of N R a])
apply (rule conjI)
 apply (simp add:sprod_mHom_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule_tac x = m and y = n in ag_pOp_closed, assumption+)
 apply (simp add:sprod_mHom_def)
apply (subst mHom_add [of N f], assumption+)
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+, 
        frule_tac f = f and m = n in mHom_mem [of N], assumption+)
 apply (simp add:Module.sc_r_distr)

apply (rule ballI)+
 apply (simp add:sprod_mHom_def)
 apply (frule_tac a = aa and m = m in sc_mem, assumption+, simp)
 apply (simp add:mHom_lin) 
 apply (frule_tac f = f and m = m in mHom_mem [of N], assumption+)
apply (simp add:Module.sc_assoc[THEN sym, of N R]) 
apply (cut_tac sc_Ring, simp add:Ring.ring_tOp_commute)
done

lemma (in Module) HOM_is_module:"R module N \<Longrightarrow> R module (HOM\<^bsub>R\<^esub> M N)"
apply (rule Module.intro)
apply (simp add:HOM_is_ag)
apply (rule Module_axioms.intro)
 apply (simp add:sc_Ring)

 apply (simp add:HOM_def)
 apply (simp add:sprod_mHom_closed)

 apply (simp add:HOM_def)
 apply (cut_tac sc_Ring,
        frule Ring.ring_is_ag[of R],
        frule_tac x = a and y = b in aGroup.ag_pOp_closed[of R], assumption+,
        frule_tac a = "a \<plusminus>\<^bsub>R\<^esub> b" and f = m in sprod_mHom_closed[of N], 
        assumption+)
  apply(frule_tac a = a and f = m in sprod_mHom_closed[of N], assumption+,
        frule_tac a = b and f = m in sprod_mHom_closed[of N], assumption+,
        frule_tac f = "sprod_mHom R M N a m" and g = "sprod_mHom R M N b m" in
        tOp_mHom_closed[of N], assumption+)
  apply (rule mHom_eq[of N], assumption+, rule ballI,
         simp add:sprod_mHom_def tOp_mHom_def)
  apply (rename_tac a b f m)
  apply (frule_tac f = f and m = m in mHom_mem[of N], assumption+)
  apply (simp add:Module.sc_l_distr[of N])

apply (simp add:HOM_def)
 apply (rename_tac a f g,
        frule_tac f = f and g = g in tOp_mHom_closed[of N], assumption+,
        frule_tac a = a and f = "tOp_mHom R M N f g" in 
                                     sprod_mHom_closed[of N], assumption+,
        frule_tac a = a and f = f in sprod_mHom_closed[of N], assumption+,
        frule_tac a = a and f = g in sprod_mHom_closed[of N], assumption+,
        frule_tac f = "sprod_mHom R M N a f" and g = "sprod_mHom R M N a g" 
        in tOp_mHom_closed[of N], assumption+)   
 apply (rule mHom_eq[of N], assumption+, rule ballI,
        simp add:sprod_mHom_def tOp_mHom_def,
        frule_tac f = f and m = m in mHom_mem[of N], assumption+,
        frule_tac f = g and m = m in mHom_mem[of N], assumption+)
 apply (simp add:Module.sc_r_distr)

apply (simp add:HOM_def)
 apply (rename_tac a b f)
 apply (cut_tac sc_Ring,
        frule_tac x = a and y = b in Ring.ring_tOp_closed, assumption+,
        frule_tac a = "a \<cdot>\<^sub>r\<^bsub>R\<^esub> b" and f = f in sprod_mHom_closed[of N], 
                                                            assumption+,
        frule_tac a = b and f = f in sprod_mHom_closed[of N], assumption+,
        frule_tac a = a and f = "sprod_mHom R M N b f" in 
                                     sprod_mHom_closed[of N], assumption+) 
 apply (rule mHom_eq[of N], assumption+, rule ballI,
        simp add:sprod_mHom_def,
        frule_tac f = f and m = m in mHom_mem[of N], assumption+,
        simp add:Module.sc_assoc)

apply (simp add:HOM_def)
 apply (cut_tac sc_Ring,
        frule Ring.ring_one,
        frule_tac a = "1\<^sub>r\<^bsub>R\<^esub>" and f = m in sprod_mHom_closed[of N], assumption+)
 apply (rule mHom_eq, assumption+, rule ballI, rename_tac f m,
        simp add:sprod_mHom_def,
        frule_tac f = f and m = m in mHom_mem[of N], assumption+,
        simp add:Module.sprod_one)
done

section "Injective hom, surjective hom, bijective hom and inverse hom"

definition
  invmfun :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
              ('c, 'b, 'm2) Module_scheme, 'a \<Rightarrow> 'c] \<Rightarrow> 'c \<Rightarrow> 'a" where
  "invmfun R M N (f :: 'a \<Rightarrow> 'c) =
                    (\<lambda>y\<in>(carrier N). SOME x. (x \<in> (carrier M) \<and> f x = y))"

definition
  misomorphic :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
              ('c, 'b, 'm2) Module_scheme] \<Rightarrow> bool" where
  "misomorphic R M N \<longleftrightarrow> (\<exists>f. f \<in> mHom R M N \<and> bijec\<^bsub>M,N\<^esub> f)"

definition
  mId :: "('a, 'b, 'm1) Module_scheme \<Rightarrow> 'a \<Rightarrow> 'a"   ("(mId\<^bsub>_\<^esub>/ )" [89]88) where
  "mId\<^bsub>M\<^esub> = (\<lambda>m\<in>carrier M. m)"

definition
  mcompose :: "[('a, 'r, 'm1) Module_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c" where
  "mcompose M g f = compose (carrier M) g f"

abbreviation
  MISOM  ("(3_ \<cong>\<^bsub>_\<^esub> _)" [82,82,83]82) where
  "M \<cong>\<^bsub>R\<^esub> N == misomorphic R M N"

lemma (in Module) minjec_inj:"\<lbrakk>R module N; injec\<^bsub>M,N\<^esub> f\<rbrakk> \<Longrightarrow>
                            inj_on f (carrier M)" 
apply (simp add:inj_on_def, (rule ballI)+, rule impI)
 apply (simp add:injec_def, erule conjE)
 apply (frule Module.module_is_ag[of N])
 apply (cut_tac module_is_ag) 
 apply (frule_tac a = x in aHom_mem[of M N f], assumption+,
        frule_tac a = y in aHom_mem[of M N f], assumption+)
 apply (simp add:aGroup.ag_eq_diffzero[of N])
 apply (simp add:aHom_inv_inv[THEN sym, of M N f],
       frule_tac x = y in aGroup.ag_mOp_closed, assumption+,
       simp add:aHom_add[THEN sym, of M N f])
 apply (simp add:ker_def)
 apply (frule_tac x = x and y = "-\<^sub>a y" in ag_pOp_closed, assumption+)
 apply (subgoal_tac "(x \<plusminus> -\<^sub>a y) \<in> {a \<in> carrier M. f a = \<zero>\<^bsub>N\<^esub>}", simp)
 apply (simp add:ag_eq_diffzero)
 apply blast
done 

lemma (in Module) invmfun_l_inv:"\<lbrakk>R module N; bijec\<^bsub>M,N\<^esub> f; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                            (invmfun R M N f) (f m) = m"
apply (simp add:bijec_def, erule conjE)
apply (frule minjec_inj [of N f], assumption+)
apply (simp add:surjec_def, erule conjE, simp add:aHom_def)
apply (frule conjunct1) 
apply (thin_tac "f \<in> carrier M \<rightarrow> carrier N \<and>
     f \<in> extensional (carrier M) \<and>
     (\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f (a \<plusminus> b) = f a \<plusminus>\<^bsub>N\<^esub> f b)")
apply (frule invfun_l [of "f" "carrier M" "carrier N" "m"], assumption+)
 apply (simp add:surj_to_def) 
apply (simp add:invfun_def invmfun_def)
done
 
lemma (in Module) invmfun_mHom:"\<lbrakk>R module N; bijec\<^bsub>M,N\<^esub> f; f \<in> mHom R M N \<rbrakk> \<Longrightarrow>
                 invmfun R M N f \<in> mHom R N M"
apply (frule minjec_inj [of N f])
 apply (simp add:bijec_def)
 apply (subgoal_tac "surjec\<^bsub>M,N\<^esub> f") prefer 2 apply (simp add:bijec_def)
 apply (rule Module.mHom_test) apply assumption apply (rule Module_axioms)

apply (rule conjI) 
 apply (simp add:surjec_def, erule conjE)
 apply (simp add:aHom_def, frule conjunct1)
 apply (thin_tac "f \<in> carrier M \<rightarrow> carrier N \<and>
     f \<in> extensional (carrier M) \<and>
     (\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f (a \<plusminus> b) = f a \<plusminus>\<^bsub>N\<^esub> f b)")
 apply (frule inv_func [of "f" "carrier M" "carrier N"], assumption+)
 apply (simp add:invmfun_def invfun_def)

apply (rule conjI)
 apply (simp add:invmfun_def restrict_def extensional_def)

apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:surjec_def)
 apply (erule conjE, simp add:surj_to_def)
 apply (frule sym, thin_tac "f ` carrier M = carrier N", simp,
        thin_tac "carrier N = f ` carrier M")
 apply (simp add:image_def, (erule bexE)+, simp)
 apply (simp add:mHom_add[THEN sym])
 apply (frule_tac x = x and y = xa in ag_pOp_closed, assumption+)
 apply (simp add:invmfun_l_inv)

apply (rule ballI)+
 apply (simp add:surjec_def, erule conjE)
 apply (simp add:surj_to_def, frule sym, thin_tac "f ` carrier M = carrier N") 
 apply (simp add:image_def, (erule bexE)+, simp)
 apply (simp add:mHom_lin[THEN sym])
 apply (frule_tac a = a and m = x in sc_mem, assumption+)
 apply (simp add:invmfun_l_inv)
done

lemma (in Module) invmfun_r_inv:"\<lbrakk>R module N; bijec\<^bsub>M,N\<^esub> f; n \<in> carrier N\<rbrakk> \<Longrightarrow>
                           f ((invmfun R M N f) n) = n"
apply (frule minjec_inj[of N f])
 apply (simp add:bijec_def)
 apply (unfold bijec_def, frule conjunct2, fold bijec_def)
 apply (simp add:surjec_def, erule conjE, simp add:surj_to_def)
 apply (frule sym, thin_tac "f ` carrier M = carrier N", simp,
        thin_tac "carrier N = f ` carrier M")
 apply (simp add:image_def, erule bexE, simp)
 apply (simp add:invmfun_l_inv)
done

lemma (in Module) mHom_compos:"\<lbrakk>R module L; R module N; f \<in> mHom R L M; 
       g \<in> mHom R M N \<rbrakk> \<Longrightarrow> compos L g f \<in> mHom R L N" 
apply (simp add:mHom_def [of "R" "L" "N"])
 apply (frule Module.module_is_ag [of L],
        frule Module.module_is_ag [of N])

apply (rule conjI) 
 apply (simp add:mHom_def, (erule conjE)+)
   apply (rule aHom_compos[of L M N f], assumption+)
   apply (cut_tac module_is_ag, assumption+)

apply (rule ballI)+
apply (simp add:compos_def compose_def)
 apply (simp add:Module.sc_mem)
 apply (subst Module.mHom_lin[of L R M _ f], assumption, rule Module_axioms, assumption+) (*apply (
        simp add:Module_def, rule conjI, assumption+) *)
 apply (subst Module.mHom_lin[of M R N _ g], rule Module_axioms, assumption) (*apply (
        simp add:Module_def, rule conjI)*)  (** ordering **)
 apply (rule Module.mHom_mem[of L R M f], assumption, rule Module_axioms, assumption+) 
 apply simp
done

lemma (in Module) mcompos_inj_inj:"\<lbrakk>R module L; R module N; f \<in> mHom R L M; 
       g \<in> mHom R M N; injec\<^bsub>L,M\<^esub> f; injec\<^bsub>M,N\<^esub> g \<rbrakk> \<Longrightarrow> injec\<^bsub>L,N\<^esub> (compos L g f)"
apply (frule Module.module_is_ag [of L],
       frule Module.module_is_ag [of N])
apply (simp add:injec_def [of "L" "N"])
apply (rule conjI)
 apply (simp add:injec_def, (erule conjE)+,
        rule_tac aHom_compos[of L M N], assumption+,
        rule module_is_ag)
 apply assumption+
 apply (simp add:compos_def compose_def)
 apply (rule equalityI)
 apply (rule subsetI, simp) 
 apply (simp add:injec_def [of _ _ "g"], erule conjE, simp add:ker_def)
 apply (subgoal_tac "f x \<in> {a. a \<in> carrier M \<and> g a = \<zero>\<^bsub>N\<^esub>}")
 apply simp
 apply (simp add:injec_def [of _ _ "f"], erule conjE)
 apply (subgoal_tac "x \<in> ker\<^bsub>L,M\<^esub> f", simp, thin_tac "ker\<^bsub>L,M\<^esub> f = {\<zero>\<^bsub>L\<^esub>}")
 apply (simp add:ker_def)
 apply (thin_tac "{a \<in> carrier M. g a = \<zero>\<^bsub>N\<^esub>} = {\<zero>}")
 apply (simp, erule conjE, simp)
 apply (rule Module.mHom_mem[of L R M f], assumption, rule Module_axioms, assumption+) 

apply (rule subsetI, simp)
 apply (frule Module.module_inc_zero [of L R])
 apply (frule Module.mHom_0[of L R M f], rule Module_axioms, assumption+) 
 apply (simp add:ker_def)
 apply (subst mHom_0[of N], assumption+, simp)
done

lemma (in Module) mcompos_surj_surj:"\<lbrakk>R module L; R module N; surjec\<^bsub>L,M\<^esub> f;
        surjec\<^bsub>M,N\<^esub> g; f \<in> mHom R L M; g \<in> mHom R M N \<rbrakk> \<Longrightarrow> 
                                        surjec\<^bsub>L,N\<^esub> (compos L g f)"
apply (frule Module.module_is_ag [of L],
       frule Module.module_is_ag [of N],
       cut_tac module_is_ag)
apply (simp add:surjec_def [of "L" "N"])
apply (rule conjI)
 apply (simp add:mHom_def, (erule conjE)+)
 apply (rule aHom_compos[of L M N f g], assumption+)

apply (rule surj_to_test)
 apply (cut_tac Module.mHom_compos [of M R L N f g]) 
 apply (simp add:mHom_def aHom_def) 
 apply (rule Module_axioms, assumption+)

apply (rule ballI)
 apply (simp add: compos_def compose_def)
 apply (simp add:surjec_def [of _ _ "g"])
 apply (erule conjE) apply (simp add:surj_to_def)
 apply (frule sym, thin_tac "g ` carrier M = carrier N", simp add:image_def,
        thin_tac "carrier N = {y. \<exists>x\<in>carrier M. y = g x}",
        erule bexE, simp)
  apply (simp add:surjec_def [of _ _ "f"], erule conjE, simp add:surj_to_def,
         rotate_tac -1, frule sym, thin_tac "f ` carrier L = carrier M",
          simp add:image_def, erule bexE, simp)
 apply blast
done

lemma (in Module) mId_mHom:"mId\<^bsub>M\<^esub> \<in> mHom R M M"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:mId_def)
apply (simp add:mId_def extensional_def)
apply (rule ballI)+
 apply (simp add:ag_pOp_closed)
apply (rule ballI)+
 apply (simp add:mId_def)
 apply (simp add:sc_mem)
done

lemma (in Module) mHom_mId_bijec:"\<lbrakk>R module N; f \<in> mHom R M N; g \<in> mHom R N M;
      compose (carrier M) g f = mId\<^bsub>M\<^esub>; compose (carrier N) f g = mId\<^bsub>N\<^esub>\<rbrakk> \<Longrightarrow>
      bijec\<^bsub>M,N\<^esub> f"
apply (simp add:bijec_def)
apply (rule conjI)
apply (simp add:injec_def)
 apply (rule conjI)
 apply (simp add:mHom_def)
 apply (simp add:ker_def)
 apply (rule equalityI)
 apply (rule subsetI, simp, erule conjE)
 apply (frule_tac x = "f x" and y = "\<zero>\<^bsub>N\<^esub>" and f = g in eq_elems_eq_val)
 apply (frule_tac f = "compose (carrier M) g f" and g = "mId\<^bsub>M\<^esub>" and x = x in
        eq_fun_eq_val, thin_tac "compose (carrier M) g f = mId\<^bsub>M\<^esub>", 
        simp add:compose_def)
 apply (cut_tac Module.mHom_0[of N R M g], simp add:mId_def, assumption,
   rule Module_axioms, assumption) 
apply (rule subsetI, simp,
       simp add:ag_inc_zero, simp add:mHom_0)

apply (simp add:surjec_def)
 apply (rule conjI, simp add:mHom_def)
 apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
 apply (rule ballI)
  apply (frule_tac f = "compose (carrier N) f g" and g = "mId\<^bsub>N\<^esub>" and x = b in
        eq_fun_eq_val, thin_tac "compose (carrier M) g f = mId\<^bsub>M\<^esub>",
        thin_tac "compose (carrier N) f g = mId\<^bsub>N\<^esub>", 
        simp add:compose_def)
 apply (simp add:mId_def)
 apply (frule_tac m = b in Module.mHom_mem [of N R M g], rule Module_axioms, assumption+)
 apply blast
done

definition
  sup_sharp :: "[('r, 'n) Ring_scheme, ('b, 'r, 'm1) Module_scheme, 
    ('c, 'r, 'm2) Module_scheme, ('a, 'r, 'm) Module_scheme, 'b \<Rightarrow> 'c] 
     \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "sup_sharp R M N L u = (\<lambda>f\<in>mHom R N L. compos M f u)"

definition
  sub_sharp :: "[('r, 'n) Ring_scheme, ('a, 'r, 'm) Module_scheme, 
    ('b, 'r, 'm1) Module_scheme, ('c, 'r, 'm2) Module_scheme, 'b \<Rightarrow> 'c] 
     \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "sub_sharp R L M N u = (\<lambda>f\<in>mHom R L M. compos L u f)"

       (*  L
          f| u
           M \<rightarrow> N,  f \<rightarrow> u o f   *)

lemma (in Module) sup_sharp_homTr:"\<lbrakk>R module N; R module L; u \<in> mHom R M N; 
      f \<in> mHom R N L \<rbrakk> \<Longrightarrow> sup_sharp R M N L u f \<in> mHom R M L"
apply (simp add:sup_sharp_def)
apply (rule Module.mHom_compos, assumption, rule Module_axioms, assumption+) 
done

lemma (in Module) sup_sharp_hom:"\<lbrakk>R module N; R module L; u \<in> mHom R M N\<rbrakk> \<Longrightarrow> 
           sup_sharp R M N L u \<in> mHom R (HOM\<^bsub>R\<^esub> N L) (HOM\<^bsub>R\<^esub> M L)"
apply (simp add:mHom_def [of "R" "HOM\<^bsub>R\<^esub> N L"])
apply (rule conjI) 
 apply (simp add:aHom_def) 
 apply (rule conjI)
 apply (simp add:HOM_def sup_sharp_homTr)

 apply (rule conjI)
 apply (simp add:sup_sharp_def extensional_def,
        rule allI, rule impI, simp add:HOM_def)

 apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac f = a and g = b in Module.tOp_mHom_closed, assumption+)
 apply (subgoal_tac "R module M")        
 apply (frule_tac f = a in Module.sup_sharp_homTr [of M R N L u], assumption+)
 apply (frule_tac f = b in Module.sup_sharp_homTr [of M R N L u], assumption+)
 apply (frule_tac f = "tOp_mHom R N L a b" in 
                            Module.sup_sharp_homTr[of M R N L u], assumption+) 
 apply (rule Module.mHom_eq, assumption+)
 apply (rule Module.tOp_mHom_closed, assumption+)

 apply (rule ballI)
 apply (simp add:sup_sharp_def tOp_mHom_def compose_def compos_def)
 apply (simp add:mHom_mem, rule Module_axioms)

apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac a = a and f = m in Module.sprod_mHom_closed [of N R L],
                                                                assumption+)
 apply (subgoal_tac "R module M",
        frule_tac f = "sprod_mHom R N L a m" in 
                 Module.sup_sharp_homTr [of M R N L u], assumption+)
 apply (frule_tac f = m in Module.sup_sharp_homTr [of M R N L u], assumption+)
 apply (frule_tac a = a and f = "sup_sharp R M N L u m" in 
           Module.sprod_mHom_closed [of M R L], assumption+)
 apply (rule mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def sup_sharp_def compose_def compos_def)
apply (simp add:Module.mHom_mem, rule Module_axioms)
done

lemma (in Module) sub_sharp_homTr:"\<lbrakk>R module N; R module L; u \<in> mHom R M N; 
       f \<in> mHom R L M\<rbrakk> \<Longrightarrow> sub_sharp R L M N u f \<in> mHom R L N"
apply (simp add:sub_sharp_def)
apply (simp add:mHom_compos)
done

lemma (in Module) sub_sharp_hom:"\<lbrakk>R module N; R module L; u \<in> mHom R M N\<rbrakk> \<Longrightarrow> 
          sub_sharp R L M N u \<in> mHom R (HOM\<^bsub>R\<^esub> L M) (HOM\<^bsub>R\<^esub> L N)"
apply (simp add:mHom_def [of _ "HOM\<^bsub>R\<^esub> L M"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:HOM_def)
 apply (simp add:sub_sharp_homTr)

apply (rule conjI)
 apply (simp add:sub_sharp_def extensional_def)
 apply (simp add:HOM_def)

apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (frule_tac f = a and g = b in Module.tOp_mHom_closed [of L R M],
   rule Module_axioms, assumption+)
 apply (subgoal_tac "R module M")
 apply (frule_tac f = "tOp_mHom R L M a b" in Module.sub_sharp_homTr 
                                 [of M R N L u], assumption+)
 apply (frule_tac f = b in Module.sub_sharp_homTr[of M R N L u],
                                                  assumption+,
        frule_tac f = a in Module.sub_sharp_homTr[of M R N L u], assumption+) 
 apply (frule_tac f = "sub_sharp R L M N u a" and 
  g = "sub_sharp R L M N u b" in Module.tOp_mHom_closed [of L R N],assumption+)
apply (rule Module.mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:tOp_mHom_def sub_sharp_def mcompose_def compose_def,
        simp add:compos_def compose_def)
 apply (rule Module.mHom_add [of M R], assumption+)
 apply (simp add:Module.mHom_mem, simp add:Module.mHom_mem)
 apply (rule Module_axioms)

apply (rule ballI)+
 apply (simp add:HOM_def)
 apply (subgoal_tac "R module M")
 apply (frule_tac a = a and f = m in Module.sprod_mHom_closed [of L R M],
                                          assumption+)
 apply (frule_tac f = "sprod_mHom R L M a m" in Module.sub_sharp_homTr 
                                 [of M R N L u], assumption+) 
 apply (frule_tac f = m in Module.sub_sharp_homTr 
                                 [of M R N L u], assumption+) 
 apply (frule_tac a = a and f = "sub_sharp R L M N u m" in 
                       Module.sprod_mHom_closed [of L R N], assumption+)
apply (rule Module.mHom_eq, assumption+)
 apply (rule ballI)
 apply (simp add:sprod_mHom_def sub_sharp_def mcompose_def compose_def)
 apply (frule_tac  f = m and m = ma in Module.mHom_mem [of L R M], assumption+)
apply (simp add:compos_def compose_def) 
apply (simp add:mHom_lin)
apply (rule Module_axioms)
done   

lemma (in Module) mId_bijec:"bijec\<^bsub>M,M\<^esub> (mId\<^bsub>M\<^esub>)" 
apply (simp add:bijec_def)
apply (cut_tac mId_mHom)
apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI) apply (simp add:mHom_def)
 apply (simp add:ker_def) apply (simp add:mId_def)
 apply (rule equalityI) apply (rule subsetI, simp) 
 apply (rule subsetI, simp, simp add:ag_inc_zero) 

apply (simp add:surjec_def)
 apply (rule conjI, simp add:mHom_def)
 apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
 apply (rule ballI)
 apply (simp add:mId_def)
done

lemma (in Module) invmfun_bijec:"\<lbrakk>R module N; f \<in> mHom R M N; bijec\<^bsub>M,N\<^esub> f\<rbrakk> \<Longrightarrow>
                  bijec\<^bsub>N,M\<^esub> (invmfun R M N f)"
apply (frule invmfun_mHom [of N f], assumption+)
apply (simp add:bijec_def [of N M])
apply (rule conjI)
apply (simp add:injec_def)
 apply (simp add:mHom_def [of "R" "N" "M"]) apply (erule conjE)+
 apply (thin_tac "\<forall>a\<in>carrier R.
        \<forall>m\<in>carrier N. invmfun R M N f (a \<cdot>\<^sub>s\<^bsub>N\<^esub> m) = a \<cdot>\<^sub>s invmfun R M N f m")
 apply (rule equalityI) apply (rule subsetI) apply (simp add:ker_def CollectI)
 apply (erule conjE)
 apply (frule_tac x = "invmfun R M N f x" and y = "\<zero>" and f = f in 
       eq_elems_eq_val,
       thin_tac "invmfun R M N f x = \<zero>")
 apply (simp add:invmfun_r_inv)
  apply (simp add:mHom_0)

apply (rule subsetI, simp)
 apply (simp add:ker_def)
 apply (simp add:Module.module_inc_zero)
 apply (cut_tac ag_inc_zero,
        frule invmfun_l_inv[of N f \<zero>], assumption+)
 apply (simp add:mHom_0)

apply (simp add:surjec_def,
       frule invmfun_mHom[of N f], assumption+)
 apply (rule conjI, simp add:mHom_def)
 apply (simp add:surj_to_def)
 apply (rule equalityI, rule subsetI, simp add:image_def, erule bexE,
        simp) thm Module.mHom_mem[of N R M "invmfun R M N f"]
 apply (rule Module.mHom_mem[of N R M "invmfun R M N f"], assumption,
   rule Module_axioms, assumption+) 
 apply (rule subsetI, simp add:image_def)
 apply (frule_tac m = x in invmfun_l_inv[of N f], assumption+)
 apply (frule_tac m = x in mHom_mem[of N f], assumption+)
 apply (frule sym, thin_tac "invmfun R M N f (f x) = x", blast)
done
  
lemma (in Module) misom_self:"M \<cong>\<^bsub>R\<^esub> M"
apply (cut_tac mId_bijec)
apply (cut_tac mId_mHom)
apply (simp add:misomorphic_def)
apply blast
done

lemma (in Module) misom_sym:"\<lbrakk>R module N; M \<cong>\<^bsub>R\<^esub> N\<rbrakk> \<Longrightarrow> N \<cong>\<^bsub>R\<^esub> M"
apply (simp add:misomorphic_def [of "R" "M" "N"])
apply (erule exE, erule conjE)
apply (frule_tac f = f in invmfun_mHom [of N], assumption+)
apply (frule_tac f = f in invmfun_bijec [of N], assumption+)
apply (simp add:misomorphic_def)
apply blast
done

lemma (in Module) misom_trans:"\<lbrakk>R module L; R module N; L \<cong>\<^bsub>R\<^esub> M; M \<cong>\<^bsub>R\<^esub> N\<rbrakk> \<Longrightarrow> 
                               L \<cong>\<^bsub>R\<^esub> N"
apply (simp add:misomorphic_def)
 apply ((erule exE)+, (erule conjE)+)
 apply (subgoal_tac  "bijec\<^bsub>L,N\<^esub> (compos L fa f)")
 apply (subgoal_tac "(compos L fa f) \<in> mHom R L N")
 apply blast
 apply (rule Module.mHom_compos[of M R L N], rule Module_axioms, assumption+) 

apply (simp add:bijec_def) apply (erule conjE)+
apply (simp add:mcompos_inj_inj)                                
apply (simp add:mcompos_surj_surj)
done

definition
  mr_coset :: "['a, ('a, 'b, 'more) Module_scheme, 'a set] \<Rightarrow> 'a set" where
  "mr_coset a M H = a \<uplus>\<^bsub>M\<^esub> H"

definition
  set_mr_cos :: "[('a, 'b, 'more) Module_scheme, 'a set] \<Rightarrow> 'a set set" where
  "set_mr_cos M H = {X. \<exists>a\<in>carrier M. X = a \<uplus>\<^bsub>M\<^esub> H}"

definition
  mr_cos_sprod :: "[('a, 'b, 'more) Module_scheme, 'a set] \<Rightarrow> 
                                              'b \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mr_cos_sprod M H a X = {z. \<exists>x\<in>X. \<exists>h\<in>H. z = h \<plusminus>\<^bsub>M\<^esub> (a \<cdot>\<^sub>s\<^bsub>M\<^esub> x)}"

definition
  mr_cospOp :: "[('a, 'b, 'more) Module_scheme, 'a set] \<Rightarrow> 
                                               'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mr_cospOp M H = (\<lambda>X. \<lambda>Y. c_top (b_ag M) H X Y)"  

definition
  mr_cosmOp :: "[('a, 'b, 'more) Module_scheme, 'a set] \<Rightarrow> 
                                                  'a set \<Rightarrow> 'a set" where
  "mr_cosmOp M H = (\<lambda>X. c_iop (b_ag M) H X)"

definition
  qmodule :: "[('a, 'r, 'more) Module_scheme, 'a set] \<Rightarrow>
                 ('a set, 'r) Module" where
  "qmodule M H = \<lparr> carrier = set_mr_cos M H, pop = mr_cospOp M H, 
    mop = mr_cosmOp M H, zero = H, sprod = mr_cos_sprod M H\<rparr>"

definition
  sub_mr_set_cos :: "[('a, 'r, 'more) Module_scheme, 'a set, 'a set] \<Rightarrow>
                            'a set set" where
 "sub_mr_set_cos M H N = {X. \<exists>n\<in>N. X = n \<uplus>\<^bsub>M\<^esub> H}" 
 (* N/H, where N is a submodule *)

abbreviation
  QMODULE  (infixl "'/'\<^sub>m" 200) where
  "M /\<^sub>m H == qmodule M H"

abbreviation
  SUBMRSET  ("(3_/ \<^sub>s'/'\<^sub>_/ _)" [82,82,83]82) where
  "N \<^sub>s/\<^sub>M H == sub_mr_set_cos M H N"

lemma (in Module) qmodule_carr:"submodule R M H \<Longrightarrow>
            carrier (qmodule M H) = set_mr_cos M H"
apply (simp add:qmodule_def)
done

lemma (in Module) set_mr_cos_mem:"\<lbrakk>submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                        m \<uplus>\<^bsub>M\<^esub> H \<in> set_mr_cos M H"
apply (simp add:set_mr_cos_def) 
apply blast
done

lemma (in Module) mem_set_mr_cos:"\<lbrakk>submodule R M N; x \<in> set_mr_cos M N\<rbrakk> \<Longrightarrow>
                          \<exists>m \<in> carrier M. x = m  \<uplus>\<^bsub>M\<^esub> N"
by (simp add:set_mr_cos_def)

lemma (in Module) m_in_mr_coset:"\<lbrakk>submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                                   m \<in> m \<uplus>\<^bsub>M\<^esub> H"
apply (cut_tac module_is_ag)
apply (frule aGroup.b_ag_group)
apply (simp add:ar_coset_def)
apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
apply (simp add:submodule_def) apply (erule conjE)+ 
apply (simp add:asubGroup_def)
apply (rule Group.a_in_rcs [of "b_ag M" "H" "m"], assumption+)
done

lemma (in Module) mr_cos_h_stable:"\<lbrakk>submodule R M H; h \<in> H\<rbrakk> \<Longrightarrow>
                                                       H = h \<uplus>\<^bsub>M\<^esub> H"
apply (cut_tac module_is_ag)
apply (frule aGroup.b_ag_group [of "M"])
apply (simp add:ar_coset_def) 
apply (rule Group.rcs_Unit2[THEN sym], assumption+,
        simp add:submodule_def, (erule conjE)+, 
        simp add:asubGroup_def) 
apply assumption
done

lemma (in Module) mr_cos_h_stable1:"\<lbrakk>submodule R M H; m \<in> carrier M; h \<in> H\<rbrakk>
             \<Longrightarrow> (m \<plusminus> h) \<uplus>\<^bsub>M\<^esub> H = m \<uplus>\<^bsub>M\<^esub> H"
apply (cut_tac module_is_ag)
apply (subst aGroup.ag_pOp_commute, assumption+)
 apply (simp add:submodule_def, (erule conjE)+, simp add:subsetD)
apply (frule aGroup.b_ag_group [of "M"])
apply (simp add:ar_coset_def)
apply (simp add:aGroup.agop_gop [THEN sym])
apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
apply (simp add:submodule_def, (erule conjE)+, simp add:asubGroup_def)
apply (rule Group.rcs_fixed1 [THEN sym, of "b_ag M" "H" "m" "h"], assumption+)
done

lemma (in Module) x_in_mr_coset:"\<lbrakk>submodule R M H; m \<in> carrier M; x \<in> m \<uplus>\<^bsub>M\<^esub> H\<rbrakk>
                 \<Longrightarrow> \<exists>h\<in>H. m \<plusminus> h = x"
apply (cut_tac module_is_ag)
 apply (frule aGroup.b_ag_group [of "M"])
 apply (simp add:submodule_def, (erule conjE)+,
        simp add:asubGroup_def)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym])
 apply (simp add:aGroup.agop_gop [THEN sym])
 apply (simp add:ar_coset_def)
 apply (frule Group.rcs_tool2[of "b_ag M" H m x], assumption+,
        erule bexE)
 apply (frule sym, thin_tac "h \<cdot>\<^bsub>b_ag M\<^esub> m = x", simp)
 apply (simp add:aGroup.agop_gop)
 apply (simp add:aGroup.ag_carrier_carrier)
 apply (frule_tac c = h in subsetD[of H "carrier M"], assumption+)
 apply (subst ag_pOp_commute[of _ m], assumption+)
 apply blast
done

lemma (in Module) mr_cos_sprodTr:"\<lbrakk>submodule R M H; a \<in> carrier R; 
       m \<in> carrier M\<rbrakk> \<Longrightarrow> mr_cos_sprod M H a (m \<uplus>\<^bsub>M\<^esub> H) = (a \<cdot>\<^sub>s m) \<uplus>\<^bsub>M\<^esub> H"
apply (cut_tac module_is_ag,
       frule aGroup.b_ag_group,
       frule sc_mem[of a m], assumption)
 apply (simp add:ar_coset_def,
        simp add:mr_cos_sprod_def)
 apply (simp add:submodule_def, (erule conjE)+)
 apply (simp add:aGroup.ag_carrier_carrier [THEN sym],
        simp add:aGroup.agop_gop [THEN sym])
 apply (simp add:asubGroup_def)
apply (rule equalityI)
 apply (rule subsetI, simp) 
 apply (erule bexE)+
 apply (frule_tac x = xa in Group.rcs_tool2[of "b_ag M" H m], assumption+)
 apply (erule bexE, rotate_tac -1, frule sym, thin_tac "ha \<cdot>\<^bsub>b_ag M\<^esub> m = xa",
        simp)
 apply (simp add:aGroup.agop_gop, simp add:aGroup.ag_carrier_carrier)
 apply (frule_tac c = ha in subsetD[of H "carrier M"], assumption+,
        simp add:sc_r_distr,
        drule_tac x = a in spec,
        drule_tac a = ha in forall_spec, simp,
        frule_tac c = "a \<cdot>\<^sub>s ha" in subsetD[of H "carrier M"], assumption+,
        frule_tac c = h in subsetD[of H "carrier M"], assumption+,
        subst ag_pOp_assoc[THEN sym], assumption+)
 apply (simp add:aGroup.agop_gop[THEN sym], 
        simp add:aGroup.ag_carrier_carrier[THEN sym]) 
 apply (frule_tac x = h and y = "a \<cdot>\<^sub>s ha" in 
                  Group.sg_mult_closed[of "b_ag M" H], assumption+)
 apply (frule_tac a = "a \<cdot>\<^sub>s m" and h = "h \<cdot>\<^bsub>b_ag M\<^esub> (a \<cdot>\<^sub>s ha)" in 
                  Group.rcs_fixed1[of "b_ag M" H], assumption+)
 apply simp
 apply (rule Group.a_in_rcs [of "b_ag M" "H"], assumption+)
 apply (simp add:aGroup.agop_gop, simp add:aGroup.ag_carrier_carrier)  
 apply (rule ag_pOp_closed, simp add:subsetD, assumption)

apply (rule subsetI, simp,
       frule_tac x = x in Group.rcs_tool2[of "b_ag M" H "a \<cdot>\<^sub>s m"], assumption+,
       erule bexE,
       rotate_tac -1, frule sym, thin_tac "h \<cdot>\<^bsub>b_ag M\<^esub> (a \<cdot>\<^sub>s m) = x",
       frule Group.a_in_rcs[of "b_ag M" H m], assumption+)
 apply blast
done

lemma (in Module) mr_cos_sprod_mem:"\<lbrakk>submodule R M H; a \<in> carrier R; 
       X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> mr_cos_sprod M H a X \<in> set_mr_cos M H"
apply (simp add:set_mr_cos_def)
 apply (erule bexE, rename_tac m, simp) 
 apply (subst mr_cos_sprodTr, assumption+)
 apply (frule_tac m = m in sc_mem [of a], assumption)
apply blast
done  

lemma (in Module) mr_cos_sprod_assoc:"\<lbrakk>submodule R M H; a \<in> carrier R;
 b \<in> carrier R; X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> mr_cos_sprod  M H (a \<cdot>\<^sub>r\<^bsub>R\<^esub> b) X = 
                           mr_cos_sprod M H a (mr_cos_sprod M H b X)"
apply (simp add:set_mr_cos_def, erule bexE, simp)
 apply (frule_tac m = aa in sc_mem [of b], assumption)
 apply (cut_tac sc_Ring,
        frule Ring.ring_tOp_closed [of "R" "a" "b"], assumption+)
 apply (subst mr_cos_sprodTr, assumption+)+
 apply (simp add: sc_assoc)
done

lemma (in Module) mr_cos_sprod_one:"\<lbrakk>submodule R M H; X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow>
                   mr_cos_sprod M H (1\<^sub>r\<^bsub>R\<^esub>) X = X"
apply (simp add:set_mr_cos_def, erule bexE, simp,
       thin_tac "X = a \<uplus>\<^bsub>M\<^esub> H")
 apply (cut_tac sc_Ring,
        frule Ring.ring_one[of "R"])
 apply (subst mr_cos_sprodTr, assumption+) 
 apply (simp add:sprod_one)
done

lemma (in Module) mr_cospOpTr:"\<lbrakk>submodule R M H; m \<in> carrier M; n \<in> carrier M\<rbrakk>
        \<Longrightarrow> mr_cospOp M H (m \<uplus>\<^bsub>M\<^esub> H) (n \<uplus>\<^bsub>M\<^esub> H) = (m \<plusminus> n) \<uplus>\<^bsub>M\<^esub> H" 
apply (cut_tac module_is_ag, frule aGroup.b_ag_group) 
apply (simp add:mr_cospOp_def mr_coset_def agop_gop [THEN sym])
apply (simp add:ag_carrier_carrier [THEN sym])

apply (simp add:submodule_def, (erule conjE)+,
       frule aGroup.asubg_nsubg, assumption+, simp add:ar_coset_def)
apply (simp add:Group.c_top_welldef[THEN sym, of "b_ag M" H m n])
done

lemma(in Module) mr_cos_sprod_distrib1:"\<lbrakk>submodule R M H; a \<in> carrier R; 
                b \<in> carrier R;  X \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> 
                mr_cos_sprod M H (a \<plusminus>\<^bsub>R\<^esub> b) X =  
                 mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H b X)"
apply (simp add:set_mr_cos_def, erule bexE, rename_tac m)
 apply simp
 apply (cut_tac sc_Ring,
        frule Ring.ring_is_ag[of R])
 apply (frule aGroup.ag_pOp_closed [of R a b], assumption+)
apply (subst mr_cos_sprodTr [of H], assumption+)+
apply (subst mr_cospOpTr, assumption+)
 apply (simp add:sc_mem, simp add:sc_mem)
 apply (simp add:sc_l_distr)
done

lemma (in Module) mr_cos_sprod_distrib2:"\<lbrakk>submodule R M H; 
 a \<in> carrier R; X \<in> set_mr_cos M H; Y \<in> set_mr_cos M H\<rbrakk> \<Longrightarrow> 
 mr_cos_sprod M H a (mr_cospOp M H X Y) =  
           mr_cospOp M H (mr_cos_sprod M H a X) (mr_cos_sprod M H a Y)"
apply (simp add:set_mr_cos_def, (erule bexE)+, rename_tac m n, simp,
       thin_tac "X = m \<uplus>\<^bsub>M\<^esub> H", thin_tac "Y = n \<uplus>\<^bsub>M\<^esub> H")
apply (subst mr_cos_sprodTr [of H], assumption+)+
 apply (subst mr_cospOpTr, assumption+)
 apply (subst mr_cospOpTr, assumption+)
 apply (simp add:sc_mem)+
apply (subst mr_cos_sprodTr [of H], assumption+)
 apply (rule ag_pOp_closed, assumption+)
apply (simp add:sc_r_distr)
done

lemma (in Module) mr_cosmOpTr:"\<lbrakk>submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow> 
                mr_cosmOp M H (m \<uplus>\<^bsub>M\<^esub> H) = (-\<^sub>a m) \<uplus>\<^bsub>M\<^esub> H"
apply (simp add:ar_coset_def) 
apply (cut_tac module_is_ag)
apply (frule aGroup.b_ag_group)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:agiop_giop [THEN sym])
apply (simp add:mr_cosmOp_def)
 apply (simp add:submodule_def, (erule conjE)+,
        frule aGroup.asubg_nsubg[of M H], assumption)
 apply (simp add:Group.c_iop_welldef[of "b_ag M" H m])
done

lemma (in Module) mr_cos_oneTr:"submodule R M H \<Longrightarrow> H =  \<zero> \<uplus>\<^bsub>M\<^esub> H"
apply (cut_tac module_is_ag,
       cut_tac ag_inc_zero)
 apply (simp add:ar_coset_def)
 apply (frule aGroup.b_ag_group)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (subst aGroup.agunit_gone[THEN sym, of M], assumption)
 apply (subst Group.rcs_Unit1, assumption)
 apply (simp add:submodule_def, (erule conjE)+, simp add:asubGroup_def)
 apply simp
done

lemma (in Module) mr_cos_oneTr1:"\<lbrakk>submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                            mr_cospOp M H H (m \<uplus>\<^bsub>M\<^esub> H) = m \<uplus>\<^bsub>M\<^esub> H"
apply (subgoal_tac "mr_cospOp M H (\<zero> \<uplus>\<^bsub>M\<^esub> H) (m \<uplus>\<^bsub>M\<^esub> H) = m \<uplus>\<^bsub>M\<^esub> H")
apply (simp add:mr_cos_oneTr [THEN sym, of H])
apply (subst mr_cospOpTr, assumption+)
 apply (simp add:ag_inc_zero)
 apply assumption
 apply (simp add:ag_l_zero)
done

lemma (in Module) qmodule_is_ag:"submodule R M H \<Longrightarrow> aGroup (M /\<^sub>m H)"
apply (cut_tac sc_Ring)
apply (rule aGroup.intro) 
 apply (simp add:qmodule_def)
 apply (rule Pi_I)+
 apply (rename_tac X Y)
 apply (simp add:set_mr_cos_def, (erule bexE)+, rename_tac n m, simp)
 apply (subst mr_cospOpTr, assumption+,
        frule_tac x = n and y = m in ag_pOp_closed, assumption+, blast)

 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def, (erule bexE)+, rename_tac a b c m n n')
 apply (simp add:mr_cospOpTr,
        frule_tac x = m and y = n in ag_pOp_closed, assumption+,
        frule_tac x = n and y = n' in ag_pOp_closed, assumption+,
       simp add:mr_cospOpTr, simp add:ag_pOp_assoc)

 apply (simp add:qmodule_def) 
  apply (simp add:set_mr_cos_def, (erule bexE)+, rename_tac a b m n, simp)
  apply (simp add:mr_cospOpTr,
         simp add:ag_pOp_commute)

 apply (simp add:qmodule_def,
        rule Pi_I,
        simp add:set_mr_cos_def, erule bexE, simp)
 apply (subst mr_cosmOpTr, assumption+,
         frule_tac x = a in ag_mOp_closed, blast)

 apply (simp add:qmodule_def,
        simp add:set_mr_cos_def, erule bexE, simp,
        simp add:mr_cosmOpTr,
        frule_tac x = aa in ag_mOp_closed)  
 apply (simp add:mr_cospOpTr,
        frule_tac x = "-\<^sub>a aa" and y = aa in ag_pOp_closed, assumption+,
        simp add:ag_l_inv1, simp add:mr_cos_oneTr[THEN sym])
 apply (simp add:qmodule_def,
        simp add:set_mr_cos_def,
        cut_tac mr_cos_oneTr[of H],
        cut_tac ag_inc_zero, blast, assumption)

 apply (simp add:qmodule_def)
  apply (simp add:set_mr_cos_def, erule bexE, simp)
 apply (subgoal_tac "mr_cospOp M H (\<zero> \<uplus>\<^bsub>M\<^esub> H) (aa \<uplus>\<^bsub>M\<^esub> H) = aa \<uplus>\<^bsub>M\<^esub> H")
  apply (simp add:mr_cos_oneTr[THEN sym, of H])
 apply (subst mr_cospOpTr, assumption+,
        simp add:ag_inc_zero, assumption, simp add:ag_l_zero)
done

lemma (in Module) qmodule_module:"submodule R M H \<Longrightarrow> R module (M /\<^sub>m H)"
apply (rule Module.intro)
apply (simp add:qmodule_is_ag)
apply (rule Module_axioms.intro)
 apply (cut_tac sc_Ring, simp)

apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprod_mem)

apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprod_distrib1[of H])

apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprod_distrib2[of H])

apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprod_assoc)

apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprod_one)
done

definition
  indmhom :: "[('b, 'm) Ring_scheme, ('a, 'b, 'm1) Module_scheme, 
    ('c, 'b, 'm2) Module_scheme, 'a \<Rightarrow> 'c] \<Rightarrow>  'a set \<Rightarrow> 'c" where
  "indmhom R M N f = (\<lambda>X\<in> (set_mr_cos M (ker\<^bsub>M,N\<^esub> f)). f ( SOME x. x \<in> X))"

abbreviation
  INDMHOM  ("(4_\<^sup>\<flat>\<^bsub>_ _, _\<^esub>)" [92,92,92,93]92) where
  "f\<^sup>\<flat>\<^bsub>R M,N\<^esub> == indmhom R M N f"


lemma (in Module) indmhom_someTr:"\<lbrakk>R module N; f \<in> mHom R M N; 
      X \<in> set_mr_cos M (ker\<^bsub>M,N\<^esub> f)\<rbrakk> \<Longrightarrow> f (SOME xa. xa \<in> X) \<in> f `(carrier M)"
apply (simp add:set_mr_cos_def)
 apply (erule bexE, simp) 
apply (frule mker_submodule [of N f], assumption+)
apply (simp add:submodule_def) apply (erule conjE)+
apply (simp add:asubGroup_def)
 apply (thin_tac "\<forall>a m. a \<in> carrier R \<and> m \<in> ker\<^bsub>M,N\<^esub> f \<longrightarrow> a \<cdot>\<^sub>s m \<in> ker\<^bsub>M,N\<^esub> f")
 apply (cut_tac module_is_ag)
 apply (frule aGroup.b_ag_group)
apply (rule someI2_ex)
 apply (simp add:ar_coset_def)
 apply (frule_tac a = a in Group.a_in_rcs[of "b_ag M" "ker\<^bsub>M,N\<^esub> f"], 
        assumption+, simp add:ag_carrier_carrier [THEN sym], blast)
apply (simp add:ar_coset_def)
 apply (frule_tac a = a and x = x in 
                  Group.rcs_subset_elem[of "b_ag M" "ker\<^bsub>M,N\<^esub> f"], assumption+)
 apply (simp add:ag_carrier_carrier, assumption+)

apply (simp add:image_def,
       simp add:ag_carrier_carrier, blast)
done

lemma (in Module) indmhom_someTr1:"\<lbrakk>R module N; f \<in> mHom R M N; m \<in> carrier M\<rbrakk>
        \<Longrightarrow>  f (SOME xa. xa \<in> (ar_coset m M (ker\<^bsub>M,N\<^esub> f))) = f m"
apply (rule someI2_ex)
 apply (frule mker_submodule[of N f], assumption)
 apply (frule_tac m_in_mr_coset[of "ker\<^bsub>M,N\<^esub> f" m], assumption+,
        blast)

 apply (frule mker_submodule [of N f], assumption+) 
 apply (frule_tac x = x in x_in_mr_coset [of  "ker\<^bsub>M,N\<^esub> f" "m"], 
                                         assumption+, erule bexE,
        frule sym , thin_tac "m \<plusminus> h = x", simp)
 apply (simp add:ker_def, erule conjE)
 apply (subst mHom_add[of N f ], assumption+, simp)
apply (frule Module.module_is_ag [of N R])
 apply (frule mHom_mem [of "N" "f" "m"], assumption+)
apply (simp add:aGroup.ag_r_zero)
done

lemma (in Module) indmhom_someTr2:"\<lbrakk>R module N; f \<in> mHom R M N; 
       submodule R M H; m \<in> carrier M; H \<subseteq> ker\<^bsub>M,N\<^esub> f\<rbrakk> \<Longrightarrow> 
                       f (SOME xa. xa \<in> m \<uplus>\<^bsub>M\<^esub> H) = f m"
apply (rule someI2_ex)
  apply (frule_tac m_in_mr_coset[of "H" m], assumption+, blast) 
   apply (frule_tac x = x in x_in_mr_coset [of  H m], 
                                         assumption+, erule bexE,
        frule sym , thin_tac "m \<plusminus> h = x", simp)
 apply (frule_tac c = h in subsetD[of H "ker\<^bsub>M,N\<^esub> f"], assumption+)
 apply (frule mker_submodule [of N f], assumption+, 
         simp add:submodule_def[of R M "ker\<^bsub>M,N\<^esub> f"], (erule conjE)+,
        frule_tac c = h in subsetD[of "ker\<^bsub>M,N\<^esub> f" "carrier M"], assumption+)
 apply (simp add:ker_def mHom_add,
        frule_tac m = m in mHom_mem[of "N" "f"], assumption+)
 apply (frule Module.module_is_ag[of N R])
 apply (simp add:aGroup.ag_r_zero)
done

lemma (in Module) indmhomTr1:"\<lbrakk>R module N; f \<in> mHom R M N; m \<in> carrier M\<rbrakk> \<Longrightarrow>
               (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>) (m \<uplus>\<^bsub>M\<^esub> (ker\<^bsub>M,N\<^esub> f)) = f m" 
apply (simp add:indmhom_def)
apply (subgoal_tac "m \<uplus>\<^bsub>M\<^esub> ker\<^bsub>M,N\<^esub> f \<in> set_mr_cos M (ker\<^bsub>M,N\<^esub> f)", simp)
 apply (rule indmhom_someTr1, assumption+)
 apply (rule set_mr_cos_mem)
apply (rule mker_submodule, assumption+)
done

lemma (in Module) indmhomTr2:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> 
      \<Longrightarrow> (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>) \<in> set_mr_cos M (ker\<^bsub>M,N\<^esub> f) \<rightarrow> carrier N" 
 apply (rule Pi_I)
 apply (simp add:set_mr_cos_def)
 apply (erule bexE)
 apply (frule_tac m = a in indmhomTr1 [of N f], assumption+)
 apply (simp add:mHom_mem)
done

lemma (in Module) indmhom:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> 
                           \<Longrightarrow> (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>) \<in> mHom R (M /\<^sub>m (ker\<^bsub>M,N\<^esub> f)) N"
apply (simp add:mHom_def [of R "M /\<^sub>m (ker\<^bsub>M,N\<^esub> f)" N])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:qmodule_def)
 apply (simp add:indmhomTr2)

apply (rule conjI)
 apply (simp add:qmodule_def indmhom_def extensional_def) 

apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def, (erule bexE)+, simp, rename_tac  m n)
 apply (frule mker_submodule [of N f], assumption+,
        simp add:mr_cospOpTr,
        frule_tac x = m and y = n in ag_pOp_closed, assumption+)
 apply (simp add:indmhomTr1, simp add:mHom_add)

 apply (rule ballI)+ 
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def, (erule bexE)+, simp)
 apply (frule mker_submodule [of N f], assumption+,
        subst mr_cos_sprodTr [of "ker\<^bsub>M,N\<^esub> f"], assumption+,
        frule_tac a = a and m = aa in sc_mem, assumption)
 apply (simp add:indmhomTr1)
 apply (simp add:mHom_lin)
done

lemma (in Module) indmhom_injec:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
       injec\<^bsub>(M /\<^sub>m (ker\<^bsub>M,N\<^esub> f)),N\<^esub> (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>)"
apply (simp add:injec_def)
apply (frule indmhom [of N f], assumption+)
apply (rule conjI)
apply (simp add:mHom_def)
apply (simp add:ker_def [of  _ _ "f\<^sup>\<flat>\<^bsub>R M, N\<^esub>"])
apply (simp add:qmodule_def) apply (fold qmodule_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI) apply (erule conjE)
 apply (simp add:set_mr_cos_def, erule bexE, simp)
 apply (simp add:indmhomTr1)
apply (frule mker_submodule [of N f], assumption+)
 apply (rule_tac h1 = a in mr_cos_h_stable [THEN sym, of "ker\<^bsub>M,N\<^esub> f"], 
         assumption+)
 apply (simp add:ker_def)

apply (rule subsetI) apply (simp add:CollectI)
 apply (rule conjI)
 apply (simp add:set_mr_cos_def)
 apply (frule mker_submodule [of N f], assumption+)
 apply (frule mr_cos_oneTr [of "ker\<^bsub>M,N\<^esub> f"])
 apply (cut_tac  ag_inc_zero)
 apply blast
 apply (frule mker_submodule [of N f], assumption+) 
apply (subst mr_cos_oneTr [of "ker\<^bsub>M,N\<^esub> f"], assumption)
 apply (cut_tac  ag_inc_zero)        
 apply (subst indmhomTr1, assumption+)
 apply (simp add:mHom_0)
done

lemma (in Module) indmhom_surjec1:"\<lbrakk>R module N; surjec\<^bsub>M,N\<^esub> f;
 f \<in> mHom R M N\<rbrakk> \<Longrightarrow> surjec\<^bsub>(M /\<^sub>m (ker\<^bsub>M,N\<^esub> f)),N\<^esub> (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>)"
apply (simp add:surjec_def)
 apply (frule indmhom [of N f], assumption+)
 apply (rule conjI)
 apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (erule conjE) 
 apply (simp add:surj_to_def, frule sym , thin_tac "f ` carrier M = carrier N",
        simp,
        thin_tac "carrier N = f ` carrier M")
 apply (simp add:image_def, erule bexE, simp)
 apply (frule_tac m = x in indmhomTr1 [of N f], assumption+)
 apply (frule mker_submodule [of N f], assumption+)
 apply (simp add:qmodule_carr)
 apply (frule_tac m = x in set_mr_cos_mem [of "ker\<^bsub>M,N\<^esub> f"], assumption+)
apply blast
done

lemma (in Module) module_homTr:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                           f \<in> mHom R M (mimg\<^bsub>R M,N\<^esub> f)"
apply (subst mHom_def, simp add:CollectI)
 apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:mimg_def mdl_def)
apply (rule conjI)
 apply (simp add:mHom_def aHom_def extensional_def)
apply (rule ballI)+
 apply (simp add:mimg_def mdl_def)
 apply (simp add:mHom_add)
apply (rule ballI)+
 apply (simp add:mimg_def mdl_def)
 apply (simp add:mHom_lin)
done

lemma (in Module) ker_to_mimg:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                ker\<^bsub>M,mimg\<^bsub>R M,N\<^esub> f\<^esub> f = ker\<^bsub>M,N\<^esub> f"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def mimg_def mdl_def)
 apply (rule subsetI)
 apply (simp add:ker_def mimg_def mdl_def) 
done

lemma (in Module) module_homTr1:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
   (mimg\<^bsub>R (M /\<^sub>m (ker\<^bsub>M,N\<^esub> f)),N\<^esub> (f\<^sup>\<flat>\<^bsub>R M,N\<^esub>)) = mimg\<^bsub>R M,N\<^esub> f"    apply (simp add:mimg_def)
apply (subgoal_tac "f\<^sup>\<flat>\<^bsub>R M, N\<^esub> ` carrier (M /\<^sub>m (ker\<^bsub>M,N\<^esub> f))  = f ` carrier M ",
       simp)
apply (simp add:qmodule_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def set_mr_cos_def)
 apply (erule exE, erule conjE, erule bexE, simp)
 apply (simp add:indmhomTr1, blast)
apply (rule subsetI,
       simp add:image_def set_mr_cos_def, erule bexE, simp)
 apply (frule_tac m1 = xa in indmhomTr1 [THEN sym, of N f], 
                                                     assumption+)
 apply blast
done

lemma (in Module) module_Homth_1:"\<lbrakk>R module N; f \<in> mHom R M N\<rbrakk> \<Longrightarrow>
                     M /\<^sub>m (ker\<^bsub>M,N\<^esub> f) \<cong>\<^bsub>R\<^esub> mimg\<^bsub>R M,N\<^esub> f"
apply (frule surjec_to_mimg[of N f], assumption,
       frule module_homTr[of N f], assumption,
       frule mimg_module[of N f], assumption,
       frule indmhom_surjec1[of "mimg\<^bsub>R M,N\<^esub> f" f], assumption+,
       frule indmhom_injec[of "mimg\<^bsub>R M,N\<^esub> f" f], assumption+,
       frule indmhom[of "mimg\<^bsub>R M,N\<^esub> f" f], assumption+)
apply (simp add:misomorphic_def,
       simp add:bijec_def)
apply (simp add:ker_to_mimg)
apply blast
done

definition
  mpj :: "[('a, 'r, 'm) Module_scheme, 'a set] \<Rightarrow>  ('a => 'a set)" where
  "mpj M H = (\<lambda>x\<in>carrier M. x \<uplus>\<^bsub>M\<^esub> H)" 

lemma (in Module) elem_mpj:"\<lbrakk>m \<in> carrier M; submodule R M H\<rbrakk> \<Longrightarrow>
                                                 mpj M H m = m \<uplus>\<^bsub>M\<^esub> H"
by (simp add:mpj_def)

lemma (in Module) mpj_mHom:"submodule R M H \<Longrightarrow> mpj M H \<in> mHom R M (M /\<^sub>m H)"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:mpj_def qmodule_carr set_mr_cos_mem)
apply (rule conjI)
 apply (simp add:mpj_def extensional_def)
apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (simp add:mpj_def, simp add:ag_pOp_closed)
 apply (simp add:mr_cospOpTr)
apply (rule ballI)+
 apply (simp add:mpj_def sc_mem)
 apply (simp add:qmodule_def)
 apply (simp add:mr_cos_sprodTr)
done
 
lemma (in Module) mpj_mem:"\<lbrakk>submodule R M H; m \<in> carrier M\<rbrakk> \<Longrightarrow>
                                mpj M H m \<in> carrier (M /\<^sub>m H)"
apply (frule mpj_mHom[of H])
apply (rule mHom_mem [of "M /\<^sub>m H" "mpj M H" "m"])
 apply (simp add:qmodule_module) apply assumption+
done

lemma (in Module) mpj_surjec:"submodule R M H \<Longrightarrow>
                             surjec\<^bsub>M,(M /\<^sub>m H)\<^esub> (mpj M H)" 
apply (simp add:surjec_def)
apply (frule mpj_mHom [of H])
apply (rule conjI, simp add:mHom_def)
apply (rule surj_to_test,
       simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (thin_tac "mpj M H \<in> mHom R M (M /\<^sub>m H)")

 apply (simp add:qmodule_def)
apply (simp add:set_mr_cos_def, erule bexE, simp)
 apply (frule_tac m = a in elem_mpj[of _ H], assumption, blast)
done

lemma (in Module) mpj_0:"\<lbrakk>submodule R M H; h \<in> H\<rbrakk> \<Longrightarrow>
                                 mpj M H h  = \<zero>\<^bsub>(M /\<^sub>m H)\<^esub>"
apply (simp add:submodule_def, (erule conjE)+)
 apply (frule_tac c = h in subsetD[of H "carrier M"], assumption+)
 apply (subst elem_mpj[of _ H], assumption+,
        simp add:submodule_def)
 apply (simp add:qmodule_def)
 apply (rule mr_cos_h_stable[THEN sym],
        simp add:submodule_def, assumption)
done

lemma (in Module) mker_of_mpj:"submodule R M H \<Longrightarrow>
                                 ker\<^bsub>M,(M /\<^sub>m H)\<^esub> (mpj M H) = H"
apply (simp add:ker_def)
apply (rule equalityI)
apply (rule subsetI, simp, erule conjE)
 apply (simp add:elem_mpj, simp add:qmodule_def)
 apply (frule_tac m = x in m_in_mr_coset [of H], assumption+)
 apply simp
apply (rule subsetI)
 apply simp
 apply (simp add:submodule_def, (erule conjE)+)
 apply (simp add:subsetD)
 apply (subst elem_mpj,
        simp add:subsetD, simp add:submodule_def) 
 apply (simp add:qmodule_def)
 apply (rule mr_cos_h_stable[THEN sym],
        simp add:submodule_def, assumption)
done

lemma (in Module) indmhom1:"\<lbrakk>submodule R M H; R module N; f \<in> mHom R M N;  H \<subseteq> ker\<^bsub>M,N\<^esub> f\<rbrakk> \<Longrightarrow> \<exists>!g. g \<in> (mHom R (M /\<^sub>m H) N) \<and> (compos M g (mpj M H)) = f" 
apply (rule ex_ex1I)
apply (subgoal_tac "(\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) \<in> mHom R  (M /\<^sub>m H) N \<and> compos M (\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)) (mpj M H) = f")
apply blast
 apply (rule conjI)
 apply (rule Module.mHom_test)
 apply (simp add:qmodule_module, assumption+)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:qmodule_def, simp add:set_mr_cos_def, erule bexE, simp)
 apply (simp add:indmhom_someTr2, simp add:mHom_mem)

 apply (rule conjI)
 apply (simp add:qmodule_def)

 apply (rule conjI, (rule ballI)+)
 apply (simp add:qmodule_def, simp add:set_mr_cos_def, (erule bexE)+, simp)
 apply (simp add:mr_cospOpTr,
        frule_tac x = a and y = aa in ag_pOp_closed, assumption+)
  apply (simp add:indmhom_someTr2, simp add:mHom_add)
  apply (rule impI) 
  apply (frule_tac x = "a \<plusminus> aa" in bspec, assumption+, simp)

 apply ((rule ballI)+,
        simp add:qmodule_def, simp add:set_mr_cos_def, erule bexE, simp,
        simp add:mr_cos_sprodTr,
        frule_tac a = a and m = aa in sc_mem, assumption)
 apply (simp add:indmhom_someTr2, simp add:mHom_lin,
        rule impI,
        frule_tac x = "a \<cdot>\<^sub>s aa" in bspec, assumption, simp)
 apply (rule mHom_eq[of N _ f], assumption)
 apply (rule Module.mHom_compos[of "M /\<^sub>m H" R M N "mpj M H" 
         "\<lambda>X\<in>set_mr_cos M H. f (SOME x. x \<in> X)"]) apply (
        simp add:qmodule_module, rule Module_axioms, assumption,
        simp add:mpj_mHom)
 apply (rule Module.mHom_test,
        simp add:qmodule_module, assumption)
 apply (rule conjI,
        rule Pi_I,
        clarsimp simp: qmodule_def set_mr_cos_def indmhom_someTr2 mHom_mem)
 apply (rule conjI,
       simp add:qmodule_def)
 apply (rule conjI,
        (rule ballI)+, simp add:qmodule_def, simp add:set_mr_cos_def,
        (erule bexE)+, simp add:mr_cospOpTr,
        frule_tac x = a and y = aa in ag_pOp_closed, assumption+,
        simp add:indmhom_someTr2 mHom_add,
        rule impI, 
        frule_tac x = "a \<plusminus> aa" in bspec, assumption, simp) 
 apply ((rule ballI)+, simp add:qmodule_def set_mr_cos_def, erule bexE, simp,
        simp add:mr_cos_sprodTr,
        frule_tac a = a and m = aa in sc_mem, assumption,
        simp add:indmhom_someTr2 mHom_lin,
        rule impI,
        frule_tac x = "a \<cdot>\<^sub>s aa" in bspec, assumption, simp, 
        assumption+) 
 apply (rule ballI, simp add:compos_def compose_def elem_mpj,
        simp add:indmhom_someTr2,
        rule impI, simp add:set_mr_cos_def,
        frule_tac x = m in bspec, assumption, simp)
 
 apply (erule conjE)+ 
 apply (rule_tac f = g and g = y in Module.mHom_eq[of "M /\<^sub>m H" R N],
        simp add:qmodule_module, assumption+) 
 apply (rule ballI, simp add:qmodule_def, fold qmodule_def,
        simp add:set_mr_cos_def, erule bexE, simp)
 apply (rotate_tac -3, frule sym, thin_tac "compos M y (mpj M H) = f", 
        simp)
 apply (frule_tac f = "compos M g (mpj M H)" and g = "compos M y (mpj M H)"
        and x = a in eq_fun_eq_val,
        thin_tac "compos M g (mpj M H) = compos M y (mpj M H)")
 apply (simp add:compos_def compose_def elem_mpj)
done

definition
  mQmp :: "[('a, 'r, 'm) Module_scheme, 'a set, 'a set] \<Rightarrow> 
                                                   ('a set \<Rightarrow> 'a set)" where
  "mQmp M H N = (\<lambda>X\<in> set_mr_cos M H. {z. \<exists> x \<in> X. \<exists> y \<in> N. (y \<plusminus>\<^bsub>M\<^esub> x = z)})"
             (* H \<subseteq> N *)

abbreviation
  MQP  ("(3Mp\<^bsub>_  _,_\<^esub>)" [82,82,83]82) where
  "Mp\<^bsub>M H,N\<^esub> == mQmp M H N"

 (* "\<lbrakk> R Module M; H \<subseteq> N \<rbrakk> \<Longrightarrow> Mp\<^bsub>M H,N\<^esub> \<in> rHom (M /\<^sub> m H) (M /\<^sub>m N)"  *)

lemma (in Module) mQmpTr0:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N;
 m \<in> carrier M\<rbrakk> \<Longrightarrow>  mQmp M H N (m \<uplus>\<^bsub>M\<^esub> H) = m \<uplus>\<^bsub>M\<^esub> N"
apply (frule set_mr_cos_mem [of H m], assumption+)
apply (simp add:mQmp_def)
apply (rule equalityI)
 apply (rule subsetI, simp, (erule bexE)+, rotate_tac -1, frule sym,
        thin_tac "y \<plusminus> xa = x", simp)
 apply (frule_tac x = xa in x_in_mr_coset[of H m], assumption+, erule bexE,
        rotate_tac -1, frule sym, thin_tac "m \<plusminus> h = xa", simp)
 apply (unfold submodule_def, frule conjunct1, rotate_tac 1, frule conjunct1,
        fold submodule_def,
        frule_tac c = y in subsetD[of N "carrier M"], assumption+,
        frule_tac c = h in subsetD[of H "carrier M"], assumption+,
        simp add:ag_pOp_assoc[THEN sym],
        simp add:ag_pOp_commute[of _ m], simp add:ag_pOp_assoc,
        frule_tac c = h in subsetD[of H N], assumption+,
        frule_tac h = y and k = h in submodule_pOp_closed[of N], assumption+,
        frule_tac h1 = "y \<plusminus> h" in mr_cos_h_stable1[THEN sym, of N m], 
        assumption+, simp)
 apply (rule m_in_mr_coset, assumption+,
        rule ag_pOp_closed, assumption+, simp add:subsetD)

 apply (rule subsetI, simp,
        frule_tac x = x in x_in_mr_coset[of N m], assumption+,
        erule bexE, frule sym, thin_tac "m \<plusminus> h = x", simp,
        simp add:submodule_def[of R M N], frule conjunct1, fold submodule_def,
        frule_tac c = h in subsetD[of N "carrier M"], assumption+)
apply (frule_tac m_in_mr_coset[of H m], assumption+,
        subst ag_pOp_commute[of m], assumption+)
 apply blast
done

  (* show mQmp M H N is a welldefined map from M/H to M/N. step2 *)
lemma (in Module) mQmpTr1:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N;
 m \<in> carrier M; n \<in> carrier M; m \<uplus>\<^bsub>M\<^esub> H = n \<uplus>\<^bsub>M\<^esub> H\<rbrakk> \<Longrightarrow>  m \<uplus>\<^bsub>M\<^esub> N = n \<uplus>\<^bsub>M\<^esub> N"
apply (frule_tac m_in_mr_coset [of H m], assumption+)
apply simp
apply (frule_tac x_in_mr_coset [of H n m], assumption+) 
apply (erule bexE, rotate_tac -1, frule sym, thin_tac "n \<plusminus> h = m", simp)
apply (frule_tac c = h in subsetD [of "H" "N"], assumption+)
apply (rule mr_cos_h_stable1[of N n], assumption+)
done
   
lemma (in Module) mQmpTr2:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N ; 
        X \<in> carrier (M /\<^sub>m H)\<rbrakk> \<Longrightarrow> (mQmp M H N) X \<in> carrier (M /\<^sub>m N)" 
apply (simp add:qmodule_def)
apply (simp add:set_mr_cos_def)
apply (erule bexE, simp)
 apply (frule_tac m = a in mQmpTr0 [of H N], assumption+)
apply blast
done

lemma (in Module) mQmpTr2_1:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N \<rbrakk>
 \<Longrightarrow> mQmp M H N \<in> carrier (M /\<^sub>m H) \<rightarrow> carrier (M /\<^sub>m N)"
by (simp add:mQmpTr2)

lemma (in Module) mQmpTr3:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N ; 
X \<in> carrier (M /\<^sub>m H); Y \<in> carrier (M /\<^sub>m H)\<rbrakk> \<Longrightarrow> (mQmp M H N) (mr_cospOp M H X Y) = mr_cospOp M N ((mQmp M H N) X) ((mQmp M H N) Y)" 
apply (simp add:qmodule_def)
apply (simp add:set_mr_cos_def)
apply ((erule bexE)+, simp)
apply (simp add:mr_cospOpTr)
apply (frule_tac x = a and y = aa in ag_pOp_closed, assumption+)
apply (subst mQmpTr0, assumption+)+
apply (subst mr_cospOpTr, assumption+) 
apply simp
done
     
lemma (in Module) mQmpTr4:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N;
                            a \<in> N\<rbrakk> \<Longrightarrow> mr_coset a (mdl M N) H = mr_coset a M H"
apply (simp add:mr_coset_def)
 apply (unfold submodule_def[of R M N], frule conjunct1, fold submodule_def,
        frule subsetD[of N "carrier M" a], assumption+)
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule mdl_is_module[of N])
 apply (frule_tac x = x in Module.x_in_mr_coset[of "mdl M N" R H a])
 apply (simp add:submodule_of_mdl)
 apply (simp add:mdl_carrier)
 apply assumption+
 apply (erule bexE)
 apply (unfold submodule_def[of R M H], frule conjunct1, fold submodule_def)
 apply (frule_tac c = h in subsetD[of H "carrier M"], assumption+)
 apply (thin_tac "x \<in> a \<uplus>\<^bsub>mdl M N\<^esub> H", thin_tac "R module mdl M N",
        simp add:mdl_def)
 apply (frule sym, thin_tac "a \<plusminus> h = x", simp)
 apply (subst mr_cos_h_stable1[THEN sym, of H a], assumption+)
 apply (frule_tac x = a and y = h in ag_pOp_closed, assumption+)
 apply (rule m_in_mr_coset, assumption+)

apply (rule subsetI)
 apply (frule_tac x = x in x_in_mr_coset[of H a], assumption+)
 apply (erule bexE, frule sym, thin_tac "a \<plusminus> h = x", simp)
 apply (frule mdl_is_module[of N])
 apply (frule submodule_of_mdl[of H N], assumption+)
 apply (subst Module.mr_cos_h_stable1[THEN sym, of "mdl M N" R H a],
         assumption+, simp add:mdl_carrier, simp)
 apply (subgoal_tac "a \<plusminus> h = a \<plusminus>\<^bsub>mdl M N\<^esub> h", simp)
 apply (rule Module.m_in_mr_coset[of "mdl M N" R H], assumption+)
 apply (frule Module.module_is_ag[of "mdl M N" R])
 apply (rule aGroup.ag_pOp_closed, assumption,
        simp add:mdl_carrier, simp add:mdl_carrier subsetD)
 apply (subst mdl_def, simp)
done

lemma (in Module) mQmp_mHom:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow>
                  (Mp\<^bsub>M H,N\<^esub>) \<in> mHom R (M /\<^sub>m H) (M /\<^sub>m N)"
apply (simp add:mHom_def)
apply (rule conjI)  
 apply (simp add:aHom_def)
 apply (simp add:mQmpTr2_1)
apply (rule conjI)
 apply (simp add:mQmp_def extensional_def qmodule_def)
 apply (rule ballI)+
 apply (frule_tac X1 = a and Y1 = b in mQmpTr3 [THEN sym, of H N],
                                               assumption+) 
 apply (simp add:qmodule_def)

apply (rule ballI)+
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (erule bexE, simp)
 apply (subst mr_cos_sprodTr, assumption+)
 apply (frule_tac a = a and m = aa in sc_mem, assumption)
 apply (simp add:mQmpTr0)
 apply (subst mr_cos_sprodTr, assumption+)
apply simp
done
    
lemma (in Module) Mp_surjec:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow> 
                surjec\<^bsub>(M /\<^sub>m H),(M /\<^sub>m N)\<^esub> (Mp\<^bsub>M H,N\<^esub>)" 
apply (simp add:surjec_def)
 apply (frule mQmp_mHom [of H N], assumption+)
 apply (rule conjI)
 apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
 apply (rule ballI)
 apply (thin_tac "Mp\<^bsub>M  H,N\<^esub> \<in> mHom R (M /\<^sub>m H) (M /\<^sub>m N)")
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def, erule bexE, simp)
 apply (frule_tac m = a in mQmpTr0 [of H N], assumption+)
 apply blast
done

lemma (in Module) kerQmp:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> 
 \<Longrightarrow> ker\<^bsub>(M /\<^sub>m H),(M /\<^sub>m N)\<^esub> (Mp\<^bsub>M H,N\<^esub>) = carrier ((mdl M N) /\<^sub>m H)"   
apply (simp add:ker_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI, erule conjE)
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def [of "mdl M N" "H"])
 apply (simp add:set_mr_cos_def)
 apply (erule bexE, simp)
 apply (simp add:mQmpTr0)
 apply (frule_tac m = a in m_in_mr_coset[of N], assumption+, simp)
 apply (frule_tac a = a in mQmpTr4[of H N], assumption+,
        simp add:mr_coset_def,
        rotate_tac -1, frule sym,thin_tac "a \<uplus>\<^bsub>mdl M N\<^esub> H = a \<uplus>\<^bsub>M\<^esub> H",
        simp only:mdl_carrier, blast)

 apply (rule subsetI)
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def [of "mdl M N" "H"])
 apply (erule bexE, simp)
 apply (simp add:mdl_carrier)
  apply (frule_tac a = a in mQmpTr4[of H N], assumption+,
         simp add:mr_coset_def)
 apply (thin_tac "a \<uplus>\<^bsub>mdl M N\<^esub> H = a \<uplus>\<^bsub>M\<^esub> H")
 apply (unfold submodule_def[of R M N], frule conjunct1, fold submodule_def,
        frule_tac c = a in subsetD[of N "carrier M"], assumption+)
 apply (rule conjI) 
 apply (simp add:set_mr_cos_def, blast)
 apply (simp add:mQmpTr0)
  apply (simp add:mr_cos_h_stable [THEN sym])
done

lemma (in Module) misom2Tr:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow> 
            (M /\<^sub>m H) /\<^sub>m (carrier ((mdl M N) /\<^sub>m H)) \<cong>\<^bsub>R\<^esub> (M /\<^sub>m N)"
apply (frule mQmp_mHom [of H N], assumption+)
apply (frule qmodule_module [of H])
apply (frule qmodule_module [of N]) thm Module.indmhom
apply (frule Module.indmhom [of "M /\<^sub>m H" R "M /\<^sub>m N" "Mp\<^bsub>M H,N\<^esub>"], assumption+)
apply (simp add:kerQmp)
apply (subgoal_tac "bijec\<^bsub>((M /\<^sub>m H) /\<^sub>m (carrier((mdl M N) /\<^sub>m H))),(M /\<^sub>m N)
\<^esub> (indmhom R (M /\<^sub>m H) (M /\<^sub>m N) (mQmp M H N))")
apply (simp add:misomorphic_def) apply blast
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:kerQmp [THEN sym])
 apply (rule Module.indmhom_injec [of "M /\<^sub>m H" R "M /\<^sub>m N" "Mp\<^bsub>M H,N\<^esub>"], assumption+)
apply (frule Mp_surjec [of H N], assumption+)
 apply (simp add:kerQmp [THEN sym])
 apply (rule Module.indmhom_surjec1, assumption+)
done

lemma (in Module) eq_class_of_Submodule:"\<lbrakk>submodule R M H; submodule R M N; 
         H \<subseteq> N\<rbrakk> \<Longrightarrow> carrier ((mdl M N) /\<^sub>m H) = N \<^sub>s/\<^sub>M H"
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def) apply (erule bexE, simp)
 apply (frule_tac a = a in mQmpTr4 [of H N], assumption+)
 apply (simp add:mdl_def) apply (simp add:mr_coset_def)
 apply (simp add:sub_mr_set_cos_def)
 apply (simp add:mdl_carrier, blast)

apply (rule subsetI)
apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (simp add:sub_mr_set_cos_def)
 apply (erule bexE, simp add:mdl_carrier)
 apply (frule_tac a1 = n in mQmpTr4[THEN sym, of H N], assumption+)
 apply (simp add:mr_coset_def)
 apply blast
done

theorem (in Module) misom2:"\<lbrakk>submodule R M H; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow> 
                           (M /\<^sub>m H) /\<^sub>m (N \<^sub>s/\<^sub>M H) \<cong>\<^bsub>R\<^esub> (M /\<^sub>m N)"
apply (frule misom2Tr [of H N], assumption+)
apply (simp add:eq_class_of_Submodule)
done

primrec natm :: "('a, 'm) aGroup_scheme  => nat \<Rightarrow> 'a  => 'a"
where
  natm_0:  "natm M 0 x = \<zero>\<^bsub>M\<^esub>"
| natm_Suc:  "natm M (Suc n) x = (natm M n x) \<plusminus>\<^bsub>M\<^esub> x"

definition
  finitesum_base :: "[('a, 'r, 'm) Module_scheme, 'b set, 'b \<Rightarrow> 'a set]
                      \<Rightarrow> 'a set " where
  "finitesum_base M I f = \<Union>{f i | i. i \<in> I}" 

definition
  finitesum :: "[('a, 'r, 'm) Module_scheme, 'b set, 'b \<Rightarrow> 'a set]
                      \<Rightarrow> 'a set " where
  "finitesum M I f = {x. \<exists>n. \<exists>g. g \<in> {j. j \<le> (n::nat)} \<rightarrow> finitesum_base M I f
                                           \<and> x =  nsum M g n}"


lemma (in Module) finitesumbase_sub_carrier:"f \<in> I \<rightarrow> {X. submodule R M X} \<Longrightarrow>
             finitesum_base M I f \<subseteq> carrier M"
apply (simp add:finitesum_base_def)
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (erule exE, erule conjE, erule exE, erule conjE)
 apply (frule_tac x = i in funcset_mem[of f I "{X. submodule R M X}"], 
         assumption+, simp)
 apply (thin_tac "f \<in> I \<rightarrow> {X. submodule R M X}", unfold submodule_def,
        frule conjunct1, fold submodule_def, simp add:subsetD)
done

lemma (in Module) finitesum_sub_carrier:"f \<in> I \<rightarrow> {X. submodule R M X} \<Longrightarrow>
                       finitesum M I f \<subseteq> carrier M"
apply (rule subsetI, simp add:finitesum_def)
apply ((erule exE)+, erule conjE, simp)
apply (frule finitesumbase_sub_carrier)
apply (rule nsum_mem, rule allI, rule impI)
apply (frule_tac x = j and f = g and A = "{j. j \<le> n}" and
        B = "finitesum_base M I f" in funcset_mem, simp)
apply (simp add:subsetD)
done

lemma (in Module) finitesum_inc_zero:"\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {}\<rbrakk>
      \<Longrightarrow>   \<zero> \<in> finitesum M I f"
apply (simp add:finitesum_def)
apply (frule nonempty_ex)
apply (subgoal_tac "\<forall>i. i\<in>I \<longrightarrow> (\<exists>n g. g \<in> {j. j \<le> (n::nat)} \<rightarrow> 
                    finitesum_base M I f \<and> \<zero>\<^bsub>M\<^esub> = \<Sigma>\<^sub>e M g n)")
apply blast 
apply (rule allI, rule impI)
apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> (0::nat)}. \<zero>) \<in> 
                    {j. j \<le> (0::nat)} \<rightarrow> finitesum_base M I f \<and>
                    \<zero>\<^bsub>M\<^esub> = \<Sigma>\<^sub>e M (\<lambda>x\<in>{j. j \<le> (0::nat)}. \<zero>) 0")
apply blast
apply (rule conjI)
apply (rule Pi_I) 
 apply (simp add:finitesum_base_def, thin_tac "\<exists>x. x \<in> I")
 apply (frule_tac x = i in funcset_mem[of f I "{X. submodule R M X}"], 
        assumption+)
 apply (frule_tac x = i in funcset_mem [of "f" "I" "{X. submodule R M X}"],
                                              assumption+, simp)
 apply (frule_tac H = "f i" in submodule_inc_0)
 apply blast

 apply simp
done

lemma (in Module) finitesum_mOp_closed:
     "\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {}; a \<in> finitesum M I f\<rbrakk> \<Longrightarrow>
                  -\<^sub>a a \<in> finitesum M I f"
apply (simp add:finitesum_def)
apply ((erule exE)+, erule conjE)
  apply (frule finitesumbase_sub_carrier [of f I])
  apply (frule_tac f = g and A = "{j. j \<le> n}" and B = "finitesum_base M I f"
          and ?B1.0 = "carrier M" in extend_fun, assumption+)
  apply (frule sym, thin_tac "a = \<Sigma>\<^sub>e M g n")
  apply (cut_tac n = n and f = g in nsum_minus,
         rule allI, simp add:Pi_def, simp)

 apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a (g x)) \<in> {j. j \<le> n} \<rightarrow> 
                                                 finitesum_base M I f")
 apply blast
 apply (rule Pi_I, simp)
 apply (frule_tac f = g and A = "{j. j \<le> n}" and B = "finitesum_base M I f" 
        and  x = x in funcset_mem, simp)
 apply (simp add:finitesum_base_def)
 apply (erule exE, erule conjE, erule exE, erule conjE)
 apply (frule_tac f = f and A = I and B = "{X. submodule R M X}" and
  x = i in funcset_mem, assumption+, simp add:CollectI)
 apply (thin_tac "f \<in> I \<rightarrow> {X. submodule R M X}")
 apply (simp add:submodule_def, (erule conjE)+,
        frule_tac H = "f i" and x = "g x" in asubg_mOp_closed, assumption+) 
 apply blast
done

lemma (in Module) finitesum_pOp_closed:
 "\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; a \<in> finitesum M I f;  b \<in> finitesum M I f\<rbrakk>
           \<Longrightarrow>  a \<plusminus> b \<in> finitesum M I f"
apply (simp add:finitesum_def) 
apply ((erule exE)+, (erule conjE)+)
apply (frule_tac f = g and n = n and A = "finitesum_base M I f" and
       g = ga and m = na and B = "finitesum_base M I f" in jointfun_hom0,
       assumption+, simp)
apply (cut_tac finitesumbase_sub_carrier[of f I],
       cut_tac n1 = n and f1 = g and m1 = na and g1 = ga in 
                 nsum_add_nm[THEN sym], rule allI, rule impI,
       frule_tac x = j and f = g and A = "{j. j \<le> n}" and
        B = "finitesum_base M I f" in funcset_mem, simp,
       simp add:subsetD,
       rule allI, rule impI,
       frule_tac x = j and f = ga and A = "{j. j \<le> na}" and
        B = "finitesum_base M I f" in funcset_mem, simp,
       simp add:subsetD)
apply blast
apply assumption
done

lemma (in Module) finitesum_sprodTr:"\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {};
       r \<in> carrier R\<rbrakk>  \<Longrightarrow> g \<in>{j. j \<le> (n::nat)} \<rightarrow> (finitesum_base M I f)
              \<longrightarrow> r \<cdot>\<^sub>s (nsum M g n) =  nsum M (\<lambda>x. r \<cdot>\<^sub>s (g x)) n"
apply (induct_tac n)
 apply (rule impI)
 apply simp
apply (rule impI)
apply (frule func_pre) apply simp
apply (frule finitesumbase_sub_carrier [of f I])
 apply (frule_tac f = g and A = "{j. j \<le> Suc n}" in extend_fun [of _ _ "finitesum_base M I f" "carrier M"], assumption+)
 apply (thin_tac "g \<in> {j. j \<le> Suc n} \<rightarrow> finitesum_base M I f",
        thin_tac "g \<in> {j. j \<le> n} \<rightarrow> finitesum_base M I f",
        frule func_pre)
 apply (cut_tac n = n in nsum_mem [of _ g])
 apply (rule allI, simp add:Pi_def)
 apply (frule_tac x = "Suc n" in funcset_mem [of "g" _ "carrier M"], simp)
 apply (subst sc_r_distr, assumption+)
 apply simp
done

lemma (in Module) finitesum_sprod:"\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {}; 
      r \<in> carrier R; g \<in>{j. j \<le> (n::nat)} \<rightarrow> (finitesum_base M I f) \<rbrakk> \<Longrightarrow>
                       r \<cdot>\<^sub>s (nsum M g n) =  nsum M (\<lambda>x. r \<cdot>\<^sub>s (g x)) n"
apply (simp add:finitesum_sprodTr)
done

lemma (in Module) finitesum_subModule:"\<lbrakk>f \<in> I \<rightarrow> {X. submodule R M X}; I \<noteq> {}\<rbrakk>
                   \<Longrightarrow> submodule R M (finitesum M I f)"
apply (simp add:submodule_def [of _ _ "(finitesum M I f)"])
apply (simp add:finitesum_sub_carrier)
apply (rule conjI)
 apply (rule asubg_test)
 apply (simp add:finitesum_sub_carrier)
 apply (frule finitesum_inc_zero, assumption, blast) 

 apply (rule ballI)+
 apply (rule finitesum_pOp_closed, assumption+,
        rule finitesum_mOp_closed, assumption+)

 apply ((rule allI)+, rule impI, erule conjE)
 apply (simp add:finitesum_def, (erule exE)+, erule conjE, simp)
 apply (simp add:finitesum_sprod)
 apply (subgoal_tac "(\<lambda>x. a \<cdot>\<^sub>s g x) \<in> {j. j \<le> n} \<rightarrow> finitesum_base M I f",
        blast)
 apply (rule Pi_I)
 apply (frule_tac x = x and f = g and A = "{j. j \<le> n}" in 
                  funcset_mem[of _ _ "finitesum_base M I f"], assumption+,
        thin_tac "g \<in> {j. j \<le> n} \<rightarrow> finitesum_base M I f",
        simp add:finitesum_base_def, erule exE, erule conjE, erule exE,
        erule conjE, simp)
 apply (frule_tac x = i and f = f and A = I in 
        funcset_mem[of _ _ "{X. submodule R M X}"], assumption+, simp,
        frule_tac H = "f i" and a = a and h = "g x" in submodule_sc_closed,
        assumption+)
apply blast
done

lemma (in Module) sSum_cont_H:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                     H \<subseteq>  H \<minusplus> K"
apply (rule subsetI)
apply (unfold submodule_def[of R M H], frule conjunct1, fold submodule_def,
       unfold submodule_def[of R M K], frule conjunct1, fold submodule_def)
apply (simp add:set_sum) 
apply (frule submodule_inc_0 [of K])
apply (cut_tac t = x in ag_r_zero [THEN sym],
       rule submodule_subset1, assumption+)
apply blast
done

lemma (in Module) sSum_commute:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                       H \<minusplus> K =  K \<minusplus> H"
apply (unfold submodule_def[of R M H], frule conjunct1, fold submodule_def,
       unfold submodule_def[of R M K], frule conjunct1, fold submodule_def)   
apply (rule equalityI)
apply (rule subsetI) 
apply (simp add:set_sum)
apply ((erule bexE)+, simp)
apply (frule_tac c = h in subsetD[of H "carrier M"], assumption+,
       frule_tac c = k in subsetD[of K "carrier M"], assumption+)
apply (subst ag_pOp_commute, assumption+)
apply blast

apply (rule subsetI)
apply (simp add:set_sum)
apply ((erule bexE)+, simp)
apply (frule_tac h = h in submodule_subset1[of K ], assumption+,
       frule_tac h = k in submodule_subset1[of H ], assumption+)
apply (subst ag_pOp_commute, assumption+)
apply blast
done

lemma (in Module) Sum_of_SubmodulesTr:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
      g \<in> {j. j \<le> (n::nat)} \<rightarrow> H \<union> K \<longrightarrow> \<Sigma>\<^sub>e M g n \<in> H \<minusplus> K"
apply (induct_tac n)
 apply (rule impI)
 apply simp
 apply (frule submodule_subset[of H],
        frule submodule_subset[of K])
 apply (simp add:set_sum)
 apply (erule disjE)
 apply (frule_tac c = "g 0" in subsetD[of H "carrier M"], assumption+,
        frule_tac t = "g 0" in ag_r_zero[THEN sym]) apply (
        frule submodule_inc_0[of K], blast)
 apply (frule_tac c = "g 0" in subsetD[of K "carrier M"], assumption+,
        frule_tac t = "g 0" in ag_l_zero[THEN sym]) apply (
        frule submodule_inc_0[of H], blast)
apply simp

apply (rule impI, frule func_pre, simp)
 apply (frule submodule_subset[of H],
        frule submodule_subset[of K])
 apply (simp add:set_sum[of H K], (erule bexE)+, simp)
 apply (frule_tac x = "Suc n" and f = g and A = "{j. j \<le> Suc n}" and
        B = "H \<union> K" in funcset_mem, simp,
        thin_tac "g \<in> {j. j \<le> n} \<rightarrow> H \<union> K",
        thin_tac "g \<in> {j. j \<le> Suc n} \<rightarrow> H \<union> K",
        thin_tac "\<Sigma>\<^sub>e M g n = h \<plusminus> k", simp)
 apply (erule disjE)
 apply (frule_tac h = h in submodule_subset1[of H], assumption,
        frule_tac h = "g (Suc n)" in submodule_subset1[of H], assumption,
        frule_tac h = k in submodule_subset1[of K], assumption) 
 apply (subst ag_pOp_assoc, assumption+)
  apply (frule_tac x = k and y = "g (Suc n)" in ag_pOp_commute, assumption+,
         simp, subst ag_pOp_assoc[THEN sym], assumption+)
  apply (frule_tac h = h and k = "g (Suc n)" in submodule_pOp_closed[of H],
         assumption+, blast)
 apply (frule_tac h = h in submodule_subset1[of H], assumption,
        frule_tac h = "g (Suc n)" in submodule_subset1[of K], assumption,
        frule_tac h = k in submodule_subset1[of K], assumption) 
 apply (subst ag_pOp_assoc, assumption+,
        frule_tac h = k and k = "g (Suc n)" in submodule_pOp_closed[of K],
         assumption+, blast)
done

lemma (in Module) sSum_two_Submodules:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                       submodule R M (H \<minusplus> K)"
apply (subst submodule_def) 
 apply (frule submodule_asubg[of H],
        frule submodule_asubg[of K])
 apply (frule plus_subgs[of H K], assumption, simp add:asubg_subset)

apply (rule allI)+
apply (rule impI, erule conjE, frule asubg_subset[of H], 
       frule asubg_subset[of K])
 apply (simp add:set_sum[of H K], (erule bexE)+, simp)
 apply (frule_tac H = H and a = a and h = h in submodule_sc_closed, 
                  assumption+,
        frule_tac H = K and a = a and h = k in submodule_sc_closed, 
                  assumption+)
 apply (frule_tac c = h in subsetD[of H "carrier M"], assumption+,
        frule_tac c = k in subsetD[of K "carrier M"], assumption+,
        simp add:sc_r_distr)
 apply blast
done

definition
  iotam :: "[('a, 'r, 'm) Module_scheme, 'a set, 'a set] \<Rightarrow> ('a \<Rightarrow> 'a)"
      ("(3\<iota>m\<^bsub>_ _,_\<^esub>)" [82, 82, 83]82) where
  "\<iota>m\<^bsub>M H,K\<^esub> = (\<lambda>x\<in>H. (x \<plusminus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>))"  (** later we define miota. This is not 
 equal to iotam **) 

lemma (in Module) iotam_mHom:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk>
                           \<Longrightarrow> \<iota>m\<^bsub>M H,K\<^esub> \<in> mHom R (mdl M H) (mdl M (H \<minusplus> K))"
apply (simp add:mHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (simp add:mdl_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:iotam_def)
 apply (frule submodule_subset[of H], frule submodule_subset[of K],
        simp add:set_sum)
 apply (frule submodule_inc_0 [of K])
 apply blast
apply (rule conjI)
 apply (simp add:iotam_def extensional_def mdl_def)
apply (rule ballI)+
 apply (simp add:mdl_def iotam_def)
 apply (frule_tac h = a and k = b in submodule_pOp_closed [of H],
                                     assumption+, simp)
 apply (frule submodule_subset[of H], 
        frule_tac c = a in subsetD[of H "carrier M"], assumption) apply (
        simp add:ag_r_zero) 
 apply ( frule_tac c = b in subsetD[of H "carrier M"], assumption,
        subst ag_pOp_assoc, assumption+,
        simp add:ag_inc_zero, simp)

apply (rule ballI)+
 apply (simp add:iotam_def mdl_def)
 apply (simp add:submodule_sc_closed)
 apply (frule submodule_inc_0[of K]) 
 apply (frule submodule_asubg[of H], frule submodule_asubg[of K],
        simp add:mem_sum_subgs)

 apply (frule_tac a = a and h = m in submodule_sc_closed, assumption+,
        frule submodule_subset[of H],
        frule_tac c = m in subsetD[of H "carrier M"], assumption+,
        frule_tac c = "a \<cdot>\<^sub>s m" in subsetD[of H "carrier M"], assumption+)
 apply (simp add:ag_r_zero)
done

lemma (in Module) mhomom3Tr:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                         submodule R (mdl M (H \<minusplus> K)) K"
apply (subst submodule_def) 
apply (rule conjI)
 apply (simp add:mdl_def)
 apply (subst sSum_commute, assumption+) 
 apply (simp add:sSum_cont_H)
apply (rule conjI)
 apply (rule aGroup.asubg_test)
 apply (frule sSum_two_Submodules [of H K], assumption+)
 apply (frule mdl_is_module [of  "(H \<minusplus> K)"])
 apply (rule Module.module_is_ag, assumption+)
apply (simp add:mdl_def)
 apply (subst sSum_commute, assumption+)   
  apply (simp add:sSum_cont_H)
 apply (frule submodule_inc_0 [of K])
 apply (simp add:nonempty)
apply (rule ballI)+
 apply (simp add:mdl_def)
 apply (rule submodule_pOp_closed, assumption+)
 apply (rule submodule_mOp_closed, assumption+)
apply ((rule allI)+, rule impI)
 apply (simp add:mdl_def, erule conjE)
 apply (frule sSum_cont_H[of K H], assumption,
        simp add:sSum_commute[of K H])
 apply (simp add:subsetD submodule_sc_closed)
done

lemma (in Module) mhomom3Tr0:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk>
     \<Longrightarrow> compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>)
        \<in> mHom R (mdl M H) (mdl M (H \<minusplus> K) /\<^sub>m K)"
apply (frule mdl_is_module [of H])
apply (frule mhomom3Tr[of H K], assumption+)
apply (frule sSum_two_Submodules [of H K], assumption+)
apply (frule mdl_is_module [of  "H \<minusplus> K"])
apply (frule iotam_mHom [of H K], assumption+) thm Module.mpj_mHom
apply (frule Module.mpj_mHom [of "mdl M (H \<minusplus> K)" R "K"], assumption+)
apply (rule  Module.mHom_compos[of "mdl M (H \<minusplus> K)" R "mdl M H"], assumption+)
apply (simp add:Module.qmodule_module, assumption)
apply (simp add:mpj_mHom)
done

lemma (in Module) mhomom3Tr1:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
  surjec\<^bsub>(mdl M H),((mdl M (H \<minusplus> K))/\<^sub>m K)\<^esub> 
    (compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>))"
apply (simp add:surjec_def)
apply (frule mhomom3Tr0 [of H K], assumption+)
apply (rule conjI)
apply (simp add:mHom_def)
apply (rule surj_to_test)
 apply (simp add:mHom_def aHom_def)
apply (rule ballI)
 apply (simp add:compos_def compose_def)
 apply (thin_tac "(\<lambda>x\<in>carrier (mdl M H). mpj (mdl M (H \<minusplus> K)) K ((\<iota>m\<^bsub>M H,K\<^esub>) x))
         \<in> mHom R (mdl M H) (mdl M (H \<minusplus> K) /\<^sub>m K)")
 apply (simp add:qmodule_def)
 apply (simp add:set_mr_cos_def)
 apply (erule bexE, simp)
 apply (simp add:mdl_carrier)
 apply (simp add:iotam_def)
 apply (simp add:mpj_def)
 apply (frule sSum_two_Submodules[of H K], assumption+)
 apply (simp add:mdl_carrier)
 apply (subgoal_tac "\<forall>aa\<in>H. aa \<plusminus> \<zero> \<in> H \<minusplus> K", simp)
 apply (frule submodule_subset[of H], frule submodule_subset[of K],
        thin_tac "\<forall>aa\<in>H. aa \<plusminus> \<zero> \<in> H \<minusplus> K",
        simp add:set_sum, (erule bexE)+) 
        apply (simp add:set_sum[THEN sym])
 apply (frule mdl_is_module[of "H \<minusplus> K"],
        frule mhomom3Tr[of H K], assumption+)
 apply (frule_tac m = h and h = k in Module.mr_cos_h_stable1[of "mdl M (H \<minusplus> K)"
        R K], assumption+)
 apply (simp add:mdl_carrier)
 apply (frule sSum_cont_H[of H K], assumption+, simp add:subsetD, assumption)
 apply (simp add:mdl_def, fold mdl_def)
 apply (subgoal_tac "\<forall>a\<in>H. a \<plusminus> \<zero> = a", simp, blast)
 apply (rule ballI)
 apply (frule_tac c = aa in subsetD[of H "carrier M"], assumption+,
        simp add:ag_r_zero)
 apply (rule ballI)
 apply (frule submodule_inc_0[of K])
 apply (rule mem_sum_subgs,
       simp add:submodule_def, simp add:submodule_def, assumption+)
done
 
lemma (in Module) mhomom3Tr2:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
  ker\<^bsub>(mdl M H),((mdl M (H \<minusplus> K)) /\<^sub>m K)\<^esub> 
    (compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>)) = H \<inter> K"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def, erule conjE)
 apply (simp add:qmodule_def)
 apply (simp add:mdl_carrier) 
 apply (simp add:compos_def compose_def mdl_def iotam_def)
 apply (fold mdl_def)
apply (simp add:iotam_def mpj_def) 
 apply (frule  sSum_two_Submodules[of H K], assumption+, simp add:mdl_carrier)
 apply (frule submodule_asubg[of H], frule submodule_asubg[of K])
 apply (frule_tac h = x and k = \<zero> in mem_sum_subgs[of H K], assumption+)
 apply (simp add:submodule_inc_0)
 apply simp apply (frule mhomom3Tr[of H K], assumption+)
 (*thm Module.m_in_mr_coset[of "mdl M (H \<minusplus> K)" R K]
 apply (frule_tac m = "x \<plusminus> \<zero>" in Module.m_in_mr_coset[of "mdl M (H \<minusplus> K)" R K])*)
apply (frule sSum_two_Submodules[of H K], assumption,
       frule mdl_is_module [of  "H \<minusplus> K"])
apply (frule_tac m = "x \<plusminus> \<zero>" in Module.m_in_mr_coset[of "mdl M (H \<minusplus> K)" R K],
                          assumption+)
 apply (simp add:mdl_carrier, simp)
 apply (frule submodule_subset[of H], 
        frule_tac c = x in subsetD[of H "carrier M"], assumption+) 
 apply (simp add:ag_r_zero)

apply (rule subsetI)
 apply (simp add:ker_def)
 apply (simp add:mdl_carrier)
 apply (simp add:qmodule_def)
 apply (simp add:compos_def compose_def)
 apply (simp add:mdl_carrier)
 apply (simp add:iotam_def mpj_def)
 apply (frule sSum_two_Submodules[of H K], assumption+)
 apply (simp add:mdl_carrier)
 apply (erule conjE,
        frule submodule_inc_0[of K],
        frule submodule_asubg[of H], frule submodule_asubg[of K],
       simp add:mem_sum_subgs)
 apply (frule submodule_subset[of K]) apply (
        frule_tac c = x in subsetD[of K "carrier M"], assumption+)
 apply (simp add:ag_r_zero,
        frule mdl_is_module [of  "H \<minusplus> K"],
        frule mhomom3Tr[of H K], assumption+)
 apply (frule_tac h1 = x in Module.mr_cos_h_stable[THEN sym, of "mdl M (H \<minusplus> K)"
         R K], assumption+)
done

lemma (in Module) mhomom_3:"\<lbrakk>submodule R M H; submodule R M K\<rbrakk> \<Longrightarrow>
                 (mdl M H) /\<^sub>m (H \<inter> K) \<cong>\<^bsub>R\<^esub> (mdl M (H \<minusplus> K)) /\<^sub>m K" 
apply (frule sSum_two_Submodules [of H K], assumption+)
 apply (frule mdl_is_module [of H])
 apply (frule mdl_is_module [of K])
 apply (frule mdl_is_module [of "H \<minusplus> K"])
 apply (frule mhomom3Tr [of H K], assumption+)
 apply (frule Module.qmodule_module [of "mdl M (H \<minusplus> K)" R K], assumption+)
apply (simp add:misomorphic_def)
apply (frule mhomom3Tr0[of H K], assumption+)
apply (frule mhomom3Tr1[of H K], assumption+)
apply (frule Module.indmhom [of "mdl M H" R "mdl M (H \<minusplus> K) /\<^sub>m K" "compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>)"], assumption+)
apply (frule Module.indmhom_injec[of "mdl M H" R "mdl M (H \<minusplus> K) /\<^sub>m K"
     "compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>)"], assumption+)
apply (frule Module.indmhom_surjec1[of  "mdl M H" R "mdl M (H \<minusplus> K) /\<^sub>m K" "compos (mdl M H) (mpj (mdl M (H \<minusplus> K)) K) (\<iota>m\<^bsub>M H,K\<^esub>)"], assumption+)
apply (simp add:bijec_def)
apply (simp add:mhomom3Tr2[of H K])
apply blast
done

definition
  l_comb :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, nat] \<Rightarrow>
    (nat \<Rightarrow> 'r) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "l_comb R M n s m = nsum M (\<lambda>j. (s j) \<cdot>\<^sub>s\<^bsub>M\<^esub> (m j)) n" 

definition
  linear_span :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 'r set,
              'a set] \<Rightarrow> 'a set" where
  "linear_span R M A H = (if H = {} then {\<zero>\<^bsub>M\<^esub>} else 
                           {x. \<exists>n. \<exists>f \<in> {j. j \<le> (n::nat)} \<rightarrow> H.
         \<exists>s\<in>{j. j \<le> (n::nat)} \<rightarrow> A.  x = l_comb R M n s f})"

definition
  coefficient :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme,
               nat, nat \<Rightarrow> 'r, nat \<Rightarrow> 'a] \<Rightarrow> nat \<Rightarrow> 'r" where
  "coefficient R M n s m j = s j"

definition
  body :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, nat, nat \<Rightarrow> 'r, 
         nat \<Rightarrow> 'a] \<Rightarrow> nat \<Rightarrow> 'a" where
  "body R M n s m j = m j"

lemma (in Module) l_comb_mem_linear_span:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> n} \<rightarrow> H\<rbrakk> \<Longrightarrow>
                    l_comb R M n s f \<in> linear_span R M A H"
apply (frule_tac x = 0 in funcset_mem[of f "{j. j \<le> n}" H], simp)
 apply (frule nonempty[of "f 0" H])
 apply (simp add:linear_span_def)
 apply blast
done

lemma (in Module) linear_comb_eqTr:"H \<subseteq> carrier M \<Longrightarrow> 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R \<and> 
      f \<in> {j. j \<le> n} \<rightarrow> H \<and> 
      g \<in> {j. j \<le> n} \<rightarrow> H \<and> 
      (\<forall>j\<in>{j. j \<le> n}. f j = g j) \<longrightarrow> 
      l_comb R M n s f = l_comb R M n s g" 
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+ apply (simp add:l_comb_def)
 
apply (rule impI) apply (erule conjE)+ 
 apply (frule_tac f = s in func_pre)
 apply (frule_tac f = f in func_pre)
 apply (frule_tac f = g in func_pre)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
        thin_tac "f \<in> {j. j \<le> n} \<rightarrow> H",
        thin_tac "g \<in> {j. j \<le> n} \<rightarrow> H")
 apply (simp add:l_comb_def)
done
           
lemma (in Module) linear_comb_eq:"\<lbrakk>H \<subseteq> carrier M; 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R; f \<in> {j. j \<le> n} \<rightarrow> H; 
       g \<in> {j. j \<le> n} \<rightarrow> H; \<forall>j\<in>{j. j \<le> n}. f j = g j\<rbrakk>  \<Longrightarrow>
  l_comb R M n s f = l_comb R M n s g" 
apply (simp add:linear_comb_eqTr)
done

lemma (in Module) l_comb_Suc:"\<lbrakk>H \<subseteq> carrier M; ideal R A; 
       s \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier R; f \<in> {j. j \<le> (Suc n)} \<rightarrow> H\<rbrakk>  \<Longrightarrow>
       l_comb R M (Suc n) s f = l_comb R M n s f \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n)" 
apply (simp add:l_comb_def)
done

lemma (in Module) l_comb_jointfun_jj:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> (n::nat)} \<rightarrow> H;
        t \<in> {j. j \<le> (m::nat)} \<rightarrow> A; g \<in> {j. j \<le> (m::nat)} \<rightarrow> H\<rbrakk> \<Longrightarrow>
        nsum M (\<lambda>j. (jointfun n s m t) j \<cdot>\<^sub>s (jointfun n f m g) j) n =
        nsum M (\<lambda>j. s j \<cdot>\<^sub>s f j) n"
apply (cut_tac sc_Ring)
apply (rule nsum_eq)
 apply (rule allI, rule impI, simp add:jointfun_def,
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI, 
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, simp add:jointfun_def)
done

lemma (in Module) l_comb_jointfun_jj1:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> (n::nat)} \<rightarrow> H;
        t \<in> {j. j \<le> (m::nat)} \<rightarrow> A; g \<in> {j. j \<le> (m::nat)} \<rightarrow> H\<rbrakk> \<Longrightarrow>
        l_comb R M n (jointfun n s m t) (jointfun n f m g) =
        l_comb R M n s f"
by (simp add:l_comb_def, simp add:l_comb_jointfun_jj)

lemma (in Module) l_comb_jointfun_jf:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> Suc (n + m)} \<rightarrow> H;
        t \<in> {j. j \<le> (m::nat)} \<rightarrow> A\<rbrakk> \<Longrightarrow>
        nsum M (\<lambda>j. (jointfun n s m t) j \<cdot>\<^sub>s f j) n =
        nsum M (\<lambda>j. s j \<cdot>\<^sub>s f j) n"
apply (cut_tac sc_Ring)
apply (rule nsum_eq)
 apply (rule allI, rule impI, simp add:jointfun_def,
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
  apply (rule allI, rule impI, 
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
  apply (rule allI, simp add:jointfun_def)
done

lemma (in Module) l_comb_jointfun_jf1:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> Suc (n + m)} \<rightarrow> H;
        t \<in> {j. j \<le> (m::nat)} \<rightarrow> A\<rbrakk> \<Longrightarrow>
        l_comb R M n (jointfun n s m t) f = l_comb R M n s f"
by (simp add:l_comb_def l_comb_jointfun_jf)

lemma (in Module) l_comb_jointfun_fj:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> Suc (n + m)} \<rightarrow> A; f \<in> {j. j \<le> (n::nat)} \<rightarrow> H;
        g \<in> {j. j \<le> (m::nat)} \<rightarrow> H\<rbrakk> \<Longrightarrow>
        nsum M (\<lambda>j. s j \<cdot>\<^sub>s (jointfun n f m g) j) n =
        nsum M (\<lambda>j. s j \<cdot>\<^sub>s f j) n"
apply (cut_tac sc_Ring)
apply (rule nsum_eq)
 apply (rule allI, rule impI, simp add:jointfun_def,
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
  apply (rule allI, rule impI, 
        rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
    apply (rule allI, simp add:jointfun_def)
done

lemma (in Module) l_comb_jointfun_fj1:"\<lbrakk>H \<subseteq> carrier M; ideal R A;
        s \<in> {j. j \<le> Suc (n + m)} \<rightarrow> A; f \<in> {j. j \<le> (n::nat)} \<rightarrow> H;
        g \<in> {j. j \<le> (m::nat)} \<rightarrow> H\<rbrakk> \<Longrightarrow>
        l_comb R M n s (jointfun n f m g) = l_comb R M n s f"
by (simp add:l_comb_def l_comb_jointfun_fj)

lemma (in Module) linear_comb0_1Tr:"H \<subseteq> carrier M \<Longrightarrow> 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> {\<zero>\<^bsub>R\<^esub>} \<and>  
      m \<in> {j. j \<le> n} \<rightarrow> H \<longrightarrow> l_comb R M n s m = \<zero>\<^bsub>M\<^esub>"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)
 apply (simp add:l_comb_def subsetD sc_0_m)

apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "{\<zero>\<^bsub>R\<^esub>}"])
 apply (frule func_pre [of _ _ "H"])
 apply simp
 apply (thin_tac "s \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}",
        thin_tac "m \<in> {j. j \<le> n} \<rightarrow> H")
 apply (simp add:l_comb_def)
 apply (frule_tac x = "Suc n" and f = s and A = "{j. j \<le> Suc n}" in 
        funcset_mem[of _ _ "{\<zero>\<^bsub>R\<^esub>}"], simp, simp,
        frule_tac x = "Suc n" and f = m and A = "{j. j \<le> Suc n}" in 
        funcset_mem[of _ _ H], simp,
        frule_tac c = "m (Suc n)" in subsetD[of H "carrier M"], assumption+,
        simp add:sc_0_m)
 apply (cut_tac ag_inc_zero)
 apply (simp add:ag_l_zero)
done

lemma (in Module) linear_comb0_1:"\<lbrakk>H \<subseteq> carrier M; 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}; m \<in> {j. j \<le> n} \<rightarrow> H \<rbrakk> \<Longrightarrow> 
      l_comb R M n s m = \<zero>\<^bsub>M\<^esub>"
apply (simp add:linear_comb0_1Tr)
done

lemma (in Module) linear_comb0_2Tr:"ideal R A \<Longrightarrow> s \<in> {j. j \<le> (n::nat)} \<rightarrow> A 
      \<and>  m \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>M\<^esub>} \<longrightarrow> l_comb R M n s m = \<zero>\<^bsub>M\<^esub>"
apply (induct_tac n )
 apply (rule impI) apply (erule conjE)
 apply (simp add:l_comb_def sc_a_0 sc_Ring Ring.ideal_subset)

apply (rule impI)
 apply (erule conjE)+
 apply (frule func_pre [of "s"],
        frule func_pre [of "m"], simp)
  apply (thin_tac "s \<in> {j. j \<le> n} \<rightarrow> A",
         thin_tac "m \<in> {j. j \<le> n} \<rightarrow> {\<zero>}")
 apply (simp add:l_comb_def)
  apply (frule_tac A = "{j. j \<le> Suc n}" and x = "Suc n" in 
         funcset_mem [of "m" _ "{\<zero>}"], simp+,
         frule_tac A = "{j. j \<le> Suc n}" and x = "Suc n" in 
         funcset_mem[of s _ A], simp+,
         cut_tac sc_Ring,
         frule_tac h = "s (Suc n)" in Ring.ideal_subset[of R A], assumption+)
  apply (cut_tac ag_inc_zero, simp add:sc_a_0)
 apply (simp add:ag_l_zero)
done

lemma (in Module) linear_comb0_2:"\<lbrakk>ideal R A;  s \<in> {j. j \<le> (n::nat)} \<rightarrow> A;
       m \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>M\<^esub>} \<rbrakk> \<Longrightarrow>  l_comb R M n s m = \<zero>\<^bsub>M\<^esub>"
apply (simp add:linear_comb0_2Tr)
done

lemma (in Module) liear_comb_memTr:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
 \<forall>s. \<forall>m. s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> 
          m \<in> {j. j \<le> n} \<rightarrow> H \<longrightarrow> l_comb R M n s m \<in> carrier M"
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (simp add: l_comb_def sc_mem Ring.ideal_subset[of R A] subsetD sc_Ring) 

apply (rule allI)+ apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"],
        frule func_pre [of _ _ "H"],
        drule_tac x = s in spec,
        drule_tac x = m in spec)

apply (simp add:l_comb_def)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule sc_mem)
 apply (cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset subsetD)
 apply (simp add:Pi_def subsetD)
done

lemma (in Module) l_comb_mem:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; m \<in> {j. j \<le> n} \<rightarrow> H\<rbrakk> \<Longrightarrow> 
      l_comb R M n s m \<in> carrier M"
apply (simp add:liear_comb_memTr)
done

lemma (in Module) l_comb_transpos:" \<lbrakk>ideal R A; H \<subseteq> carrier M;
      s \<in> {l. l \<le> Suc n} \<rightarrow> A; f \<in> {l. l \<le> Suc n} \<rightarrow> H;
      j < Suc n \<rbrakk> \<Longrightarrow> 
     \<Sigma>\<^sub>e M (cmp (\<lambda>k. s k \<cdot>\<^sub>s f k) (transpos j (Suc n))) (Suc n) =
       \<Sigma>\<^sub>e M (\<lambda>k. (cmp s (transpos j (Suc n))) k \<cdot>\<^sub>s
                  (cmp f (transpos j (Suc n))) k) (Suc n)"
apply (cut_tac sc_Ring)
apply (rule nsum_eq) 
 apply (rule allI, rule impI, simp add:cmp_def)
 apply (cut_tac l = ja in transpos_mem[of j "Suc n" "Suc n"],
        simp add:less_imp_le, simp, simp, assumption)
 apply (rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI, simp add:cmp_def)
 apply (frule less_imp_le[of j "Suc n"],
        frule_tac l = ja in transpos_mem[of j "Suc n" "Suc n"], simp,
        simp, assumption+)
 apply (rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI,
        simp add:cmp_def)
done

lemma (in Module) l_comb_transpos1:" \<lbrakk>ideal R A; H \<subseteq> carrier M;
      s \<in> {l. l \<le> Suc n} \<rightarrow> A; f \<in> {l. l \<le> Suc n} \<rightarrow> H; j < Suc n \<rbrakk> \<Longrightarrow> 
 l_comb R M (Suc n) s f = 
  l_comb R M (Suc n) (cmp s (transpos j (Suc n))) (cmp f (transpos j (Suc n)))"
apply (cut_tac sc_Ring)
apply (frule l_comb_transpos[THEN sym, of A H s n f j], assumption+)
 apply (simp del:nsum_suc add:l_comb_def,
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>k. (cmp s (transpos j (Suc n))) k \<cdot>\<^sub>s
               (cmp f (transpos j (Suc n))) k) (Suc n) =
     \<Sigma>\<^sub>e M (cmp (\<lambda>k. s k \<cdot>\<^sub>s f k) (transpos j (Suc n))) (Suc n)")
 apply (cut_tac addition2[of "\<lambda>j. s j \<cdot>\<^sub>s f j" n "transpos j (Suc n)"],
         simp)
 apply (rule Pi_I, rule sc_mem,
          simp add:Pi_def Ring.ideal_subset,
          simp add:Pi_def subsetD)
 apply (rule_tac i = j and n = "Suc n" and j = "Suc n" in transpos_hom,
        simp add:less_imp_le, simp, simp)
 apply (rule_tac i = j and n = "Suc n" and j = "Suc n" in transpos_inj,
         simp add:less_imp_le, simp, simp)
done

lemma (in Module) sc_linear_span:"\<lbrakk>ideal R A; H \<subseteq> carrier M; a \<in> A;
 h \<in> H\<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>s h \<in> linear_span R M A H"
apply (simp add:linear_span_def)
 apply (simp add:nonempty)
 apply (simp add:l_comb_def)
 apply (subgoal_tac "(\<lambda>k\<in>{j. j \<le> (0::nat)}. a) \<in>{j. j \<le> 0} \<rightarrow> A")
 apply (subgoal_tac "(\<lambda>k\<in>{j. j \<le> 0}. h) \<in> {j. j \<le> (0::nat)} \<rightarrow> H")
 apply (subgoal_tac "a \<cdot>\<^sub>s h = 
 \<Sigma>\<^sub>e M (\<lambda>j. (\<lambda>k\<in>{j. j \<le> (0::nat)}. a) j \<cdot>\<^sub>s (\<lambda>k\<in>{j. j \<le> (0::nat)}. h) j) 0")
 apply blast
 apply simp+
done

lemma (in Module) l_span_cont_H:"H \<subseteq> carrier M \<Longrightarrow> 
                      H \<subseteq> linear_span R M (carrier R) H"            
apply (rule subsetI)
apply (cut_tac sc_Ring,
       cut_tac Ring.whole_ideal[of R])
apply (frule_tac A = "carrier R" and H = H and a = "1\<^sub>r\<^bsub>R\<^esub>" 
       and h = x in sc_linear_span, assumption+)
 apply (simp add:Ring.ring_one, assumption+)
 apply (frule_tac c = x in subsetD[of H "carrier M"], assumption+,
        simp add:sprod_one, assumption)
done

lemma (in Module) linear_span_inc_0:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk>  \<Longrightarrow> 
                   \<zero> \<in> linear_span R M A H" 
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)

apply (frule nonempty_ex[of H], erule exE)
 apply (frule_tac h = x in sc_linear_span[of A H "\<zero>\<^bsub>R\<^esub>"], assumption)
 apply (cut_tac sc_Ring, simp add:Ring.ideal_zero, assumption)
 apply (frule_tac c = x in subsetD[of H "carrier M"], assumption,
        simp add:sc_0_m)
done

lemma (in Module) linear_span_iOp_closedTr1:"\<lbrakk>ideal R A;
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A\<rbrakk> \<Longrightarrow>
               (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)) \<in> {j. j \<le> n} \<rightarrow> A"
apply (rule Pi_I)
 apply simp
 apply (cut_tac sc_Ring,
        rule Ring.ideal_inv1_closed, assumption+)
 apply (simp add:Pi_def)
done

lemma (in Module) l_span_gen_mono:"\<lbrakk>K \<subseteq> H; H \<subseteq> carrier M; ideal R A\<rbrakk> \<Longrightarrow>
        linear_span R M A K \<subseteq> linear_span R M A H"
apply (rule subsetI)
apply (case_tac "K = {}", simp add:linear_span_def[of _ _ _ "{}"],
       simp add:linear_span_inc_0)
apply (frule nonempty_ex[of K], erule exE,
       frule_tac c = xa in subsetD[of K H], assumption+,
       frule nonempty[of _ H])
apply (simp add:linear_span_def[of _ _ _ K],
       erule exE, (erule bexE)+, simp,
       frule extend_fun[of _ _ K H], assumption+)
apply (simp add: l_comb_mem_linear_span)
done

lemma (in Module) l_comb_add:"\<lbrakk>ideal R A; H \<subseteq> carrier M;
        s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> n} \<rightarrow> H;
        t \<in> {j. j \<le> (m::nat)} \<rightarrow> A; g \<in> {j. j \<le> m} \<rightarrow> H\<rbrakk> \<Longrightarrow>
  l_comb R M (Suc (n + m)) (jointfun n s m t) (jointfun n f m g) =
                                  l_comb R M n s f \<plusminus> l_comb R M m t g"
apply (cut_tac sc_Ring)       
apply (simp del:nsum_suc add:l_comb_def)
 apply (subst nsum_split)
 apply (rule allI, rule impI)
 apply (case_tac "j \<le> n", simp add:jointfun_def,
        rule sc_mem, simp add:Pi_def Ring.ideal_subset,
       simp add:Pi_def subsetD)
 apply (simp add:jointfun_def sliden_def) 
 apply (frule_tac m = j and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
        thin_tac "j \<le> Suc (n + m)", simp,
        rule sc_mem, simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD) 
 apply (simp add:l_comb_jointfun_jj[of H A s n f t m g])
 apply (cut_tac nsum_eq[of m "cmp (\<lambda>j. jointfun n s m t j \<cdot>\<^sub>s 
        jointfun n f m g j) (slide (Suc n))" "\<lambda>j. t j \<cdot>\<^sub>s g j"], simp)
 apply (rule allI, rule impI, simp add:cmp_def,
        simp add:jointfun_def sliden_def slide_def,
        rule sc_mem, simp add:Pi_def Ring.ideal_subset,
       simp add:Pi_def subsetD)
 apply (rule allI, rule impI,
        rule sc_mem, simp add:Pi_def Ring.ideal_subset,
       simp add:Pi_def subsetD)
 apply (simp add:cmp_def jointfun_def sliden_def slide_def)
done
       
lemma (in Module) l_comb_add1Tr:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
  f \<in> {j. j \<le> (n::nat)} \<rightarrow> H \<and> s \<in> {j. j \<le> n} \<rightarrow> A \<and> t \<in> {j. j \<le> n} \<rightarrow> A \<longrightarrow>
    l_comb R M n (\<lambda>x\<in>{j. j \<le> n}. (s x) \<plusminus>\<^bsub>R\<^esub> (t x)) f =
      l_comb R M n s f \<plusminus> l_comb R M n t f"
apply (induct_tac n)
 apply (simp add:l_comb_def sc_Ring Ring.ideal_subset subsetD sc_l_distr)

 apply (rule impI, (erule conjE)+)
 apply (frule func_pre[of f], frule func_pre[of s], frule func_pre[of t],
        simp)
 apply (simp add:l_comb_def, cut_tac sc_Ring)
 apply (cut_tac n = n and f = "\<lambda>j. (if j \<le> n then s j \<plusminus>\<^bsub>R\<^esub> t j else undefined) \<cdot>\<^sub>s f j" and g = "\<lambda>j. (if j \<le> Suc n then s j \<plusminus>\<^bsub>R\<^esub> t j else undefined) \<cdot>\<^sub>s
                     f j" in nsum_eq)
 apply (rule allI, rule impI, simp,
         rule sc_mem, frule Ring.ring_is_ag,
         rule aGroup.ag_pOp_closed[of R], assumption,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def subsetD)
 apply (rule allI, rule impI, simp,
         rule sc_mem, frule Ring.ring_is_ag,
         rule aGroup.ag_pOp_closed[of R], assumption,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def subsetD)
 apply (simp)
 apply simp
 apply (thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. (if j \<le> n then s j \<plusminus>\<^bsub>R\<^esub> t j else undefined) \<cdot>\<^sub>s f j)
        n =  \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n",
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. (if j \<le> Suc n then s j \<plusminus>\<^bsub>R\<^esub> t j else undefined) \<cdot>\<^sub>s 
        f j) n = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n")
 apply (frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" in 
        funcset_mem[of s _ A], simp,
        frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" in 
        funcset_mem[of t _ A], simp,
        frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" in
        funcset_mem[of f _ H], simp,
        cut_tac sc_Ring,
        frule_tac h = "s (Suc n)" in Ring.ideal_subset, assumption+,
        frule_tac h = "t (Suc n)" in Ring.ideal_subset, assumption+,
        frule_tac c = "f (Suc n)" in subsetD[of H "carrier M"], assumption+)
 apply (simp add:sc_l_distr)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" in nsum_mem,
        rule allI, rule impI,  rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (cut_tac n = n and f = "\<lambda>j. t j \<cdot>\<^sub>s f j" in nsum_mem,
        rule allI, rule impI,  rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (cut_tac a = "s (Suc n)" and m = "f (Suc n)" in sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (cut_tac a = "t (Suc n)" and m = "f (Suc n)" in sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (subst pOp_assocTr41[THEN sym], assumption+,
        subst pOp_assocTr42, assumption+)
 apply (frule_tac x = "\<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n" and 
         y = "s (Suc n) \<cdot>\<^sub>s f (Suc n)" in ag_pOp_commute, assumption+, simp)
  apply (subst pOp_assocTr42[THEN sym], assumption+,
         subst pOp_assocTr41, assumption+, simp)
done

lemma (in Module) l_comb_add1:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
 f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; s \<in> {j. j \<le> n} \<rightarrow> A; t \<in> {j. j \<le> n} \<rightarrow> A \<rbrakk> \<Longrightarrow> 
   l_comb R M n (\<lambda>x\<in>{j. j \<le> n}. (s x) \<plusminus>\<^bsub>R\<^esub> (t x)) f =
                                l_comb R M n s f \<plusminus> l_comb R M n t f"
apply (simp add:l_comb_add1Tr)
done

lemma (in Module) linear_span_iOp_closedTr2:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
       f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; s \<in> {j. j \<le> n} \<rightarrow> A\<rbrakk>  \<Longrightarrow>
       -\<^sub>a (l_comb R M n s f) = 
           l_comb R M n (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)) f"
apply (frule_tac f = f and A = "{j. j \<le> n}" and B = H and x = 0 in 
       funcset_mem, simp)
apply (frule_tac A = A and s = s in linear_span_iOp_closedTr1, assumption+)
apply (frule l_comb_add1[of A H f n s "\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)"], 
        assumption+)
apply (cut_tac linear_comb0_1[of H "\<lambda>x\<in>{j. j \<le> n}. s x \<plusminus>\<^bsub>R\<^esub> 
                  (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)) x" n f])
 apply (simp,
       thin_tac "l_comb R M n
 (\<lambda>x\<in>{j. j \<le> n}. s x \<plusminus>\<^bsub>R\<^esub> (if x \<le> n then -\<^sub>a\<^bsub>R\<^esub> (s x) else undefined)) f = \<zero>")
 apply (frule l_comb_mem[of A H s n f], assumption+,
        frule l_comb_mem[of A H "\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)" n f], assumption+)
 apply (frule ag_mOp_closed[of "l_comb R M n s f"])
 apply (frule ag_pOp_assoc[of "-\<^sub>a (l_comb R M n s f)" "l_comb R M n s f" "l_comb R M n (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)) f"], assumption+)
 apply (simp, simp add:ag_l_inv1, simp add:ag_l_zero, simp add:ag_r_zero)
 apply assumption+
 apply (rule Pi_I, simp)
 apply (frule_tac x = x in funcset_mem[of s "{j. j \<le> n}" A], simp,
        cut_tac sc_Ring,
        frule_tac h = "s x" in Ring.ideal_subset[of R A], assumption+)
 apply (frule Ring.ring_is_ag[of R],
        simp add:aGroup.ag_r_inv1[of R])
 apply assumption
done

lemma (in Module) linear_span_iOp_closed:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
 a \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> -\<^sub>a a \<in> linear_span R M A H"
apply (case_tac "H = {}")
apply (simp add:linear_span_def)
apply (simp add:ag_inv_zero)
apply (simp add:linear_span_def, erule exE, (erule bexE)+)
apply simp
apply (frule_tac f = f and n = n and s = s in 
                 linear_span_iOp_closedTr2[of A H], assumption+)
apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (s x)) \<in> {j. j \<le> n} \<rightarrow> A")
apply blast
apply (rule Pi_I, simp)
apply(cut_tac sc_Ring,
      rule Ring.ideal_inv1_closed, assumption+,
      simp add:Pi_def)
done

lemma (in Module) linear_span_pOp_closed:
 "\<lbrakk>ideal R A; H \<subseteq> carrier M; a \<in> linear_span R M A H; b \<in> linear_span R M A H\<rbrakk>
  \<Longrightarrow> a \<plusminus> b \<in> linear_span R M A H"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (cut_tac ag_inc_zero, simp add:ag_r_zero)
apply (simp add:linear_span_def) 
 apply ((erule exE)+, (erule bexE)+)
 apply (rename_tac n m f g s t)
 apply (simp add:l_comb_def)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" and m = m and 
                g = "\<lambda>j. t j \<cdot>\<^sub>s g j" in nsum_add_nm)
 apply (rule allI, rule impI, rule sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI, rule sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rotate_tac -1, frule sym, 
        thin_tac "\<Sigma>\<^sub>e M (jointfun n (\<lambda>j. s j \<cdot>\<^sub>s f j) m (\<lambda>j. t j \<cdot>\<^sub>s g j)) 
                     (Suc (n + m)) =
                  \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s g j) m",
         simp del:nsum_suc)
 apply (cut_tac n = "Suc (n + m)" and f = "jointfun n (\<lambda>j. s j \<cdot>\<^sub>s f j) m 
  (\<lambda>j. t j \<cdot>\<^sub>s g j)" and g = "\<lambda>j. (jointfun n s m t) j \<cdot>\<^sub>s (jointfun n f m g) j"
   in nsum_eq)
 apply (rule allI, rule impI)
  apply (simp add:jointfun_def)
  apply (case_tac "j \<le> n", simp)
  apply (rule sc_mem,
         cut_tac sc_Ring,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def subsetD)  
  apply (simp, rule sc_mem)
  apply (simp add:sliden_def,
         frule_tac m = j and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
         thin_tac "j \<le> Suc (n + m)", simp,
         cut_tac sc_Ring,
         simp add:Pi_def Ring.ideal_subset) 
  apply (simp add:sliden_def,
         frule_tac m = j and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
         thin_tac "j \<le> Suc (n + m)", simp,
         cut_tac sc_Ring,
         simp add:Pi_def subsetD) 
 apply (rule allI, rule impI)
  apply (simp add:jointfun_def)
  apply (case_tac "j \<le> n", simp)
  apply (rule sc_mem,
         cut_tac sc_Ring,
         simp add:Pi_def Ring.ideal_subset,
         simp add:Pi_def subsetD)  
  apply (simp, simp add:sliden_def,
         rule sc_mem,
         frule_tac m = j and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
         thin_tac "j \<le> Suc (n + m)", simp,
         cut_tac sc_Ring,
         simp add:Pi_def Ring.ideal_subset) 
  apply (frule_tac m = j and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
         thin_tac "j \<le> Suc (n + m)", simp,
         cut_tac sc_Ring,
         simp add:Pi_def subsetD)
  apply (rule allI, rule impI,
         simp add:jointfun_def)
apply (simp del:nsum_suc,
       thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s g j) m =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun n s m t j \<cdot>\<^sub>s jointfun n f m g j) (Suc (n + m))",
       thin_tac "\<Sigma>\<^sub>e M (jointfun n (\<lambda>j. s j \<cdot>\<^sub>s f j) m (\<lambda>j. t j \<cdot>\<^sub>s g j))
                        (Suc (n + m)) =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun n s m t j \<cdot>\<^sub>s jointfun n f m g j) (Suc (n + m))")
 apply (frule_tac f = s and n = n and A = A and g = t and m = m and B = A in
                  jointfun_hom0, assumption+, simp del:nsum_suc,
        frule_tac f = f and n = n and A = H and g = g and m = m and B = H in
                  jointfun_hom0, assumption+, simp del:nsum_suc)
 apply blast
done

lemma (in Module) l_comb_scTr:"\<lbrakk>ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; H \<noteq> {}\<rbrakk>  \<Longrightarrow> s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> 
 g \<in> {j. j \<le> n} \<rightarrow>  H  \<longrightarrow> r \<cdot>\<^sub>s (nsum M (\<lambda>k. (s k) \<cdot>\<^sub>s (g k))  n) =  
                             nsum M (\<lambda>k. r \<cdot>\<^sub>s ((s k) \<cdot>\<^sub>s (g k))) n" 
apply (induct_tac n)
 apply (rule impI, (erule conjE)+, simp)

apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"]) apply (frule func_pre [of _ _ "H"])
 apply (simp)
 apply (cut_tac n = n and f = "\<lambda>k. s k \<cdot>\<^sub>s g k" in nsum_mem,
        rule allI, rule impI,
        cut_tac sc_Ring, rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)  
 apply (cut_tac a = "s (Suc n)" and m = "g (Suc n)" in sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)  
 apply (simp add:sc_r_distr)
done

lemma (in Module) l_comb_sc1Tr:"\<lbrakk>ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; H \<noteq> {}\<rbrakk>  \<Longrightarrow> s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> 
 g \<in> {j. j \<le> n} \<rightarrow>  H  \<longrightarrow> r \<cdot>\<^sub>s (nsum M (\<lambda>k. (s k) \<cdot>\<^sub>s (g k))  n) =  
                             nsum M (\<lambda>k. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s (g k)) n"
apply (cut_tac sc_Ring) 
apply (induct_tac n)
 apply (rule impI, (erule conjE)+, simp)
 apply (subst sc_assoc, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD, simp)

apply (rule impI) apply (erule conjE)
 apply (frule func_pre [of _ _ "A"], frule func_pre [of _ _ "H"])
 apply simp
 apply (cut_tac n = n and f = "\<lambda>k. s k \<cdot>\<^sub>s g k" in nsum_mem,
        rule allI, rule impI,
        cut_tac sc_Ring, rule sc_mem,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)  
 apply (cut_tac a = "s (Suc n)" and m = "g (Suc n)" in sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)  
 apply (simp add:sc_r_distr)
 apply (subst  sc_assoc, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD, simp)
done

lemma (in Module) l_comb_sc:"\<lbrakk>ideal R A; H \<subseteq> carrier M; r \<in> carrier R; 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> A;  g \<in> {j. j \<le> n} \<rightarrow>  H\<rbrakk> \<Longrightarrow>
r \<cdot>\<^sub>s (nsum M (\<lambda>k. (s k) \<cdot>\<^sub>s (g k)) n) = nsum M (\<lambda>k. r \<cdot>\<^sub>s ((s k) \<cdot>\<^sub>s (g k))) n" 
apply (case_tac "H \<noteq> {}")
 apply (simp add:l_comb_scTr)
 apply simp
 apply (frule_tac x = 0 in funcset_mem[of g " {j. j \<le> n}" "{}"], simp)
 apply blast
done

lemma (in Module) l_comb_sc1:"\<lbrakk>ideal R A; H \<subseteq> carrier M; r \<in> carrier R; 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> A;  g \<in> {j. j \<le> n} \<rightarrow>  H\<rbrakk> \<Longrightarrow>
r \<cdot>\<^sub>s (nsum M (\<lambda>k. (s k) \<cdot>\<^sub>s (g k)) n) = nsum M (\<lambda>k. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s (g k)) n" 
apply (case_tac "H \<noteq> {}")
 apply (simp add:l_comb_sc1Tr)
 apply simp
 apply (frule_tac x = 0 in funcset_mem[of g " {j. j \<le> n}" "{}"], simp)
 apply blast
done

lemma (in Module) linear_span_sc_closed:"\<lbrakk>ideal R A; H \<subseteq> carrier M;
 r \<in> carrier R; x \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> r \<cdot>\<^sub>s x \<in> linear_span R M A H"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:sc_a_0)
apply (simp add:linear_span_def)
 apply (erule exE, (erule bexE)+)
 apply (simp add:l_comb_def) 
 apply (simp add:l_comb_sc)
 
apply (cut_tac n = n and f = "\<lambda>j. r \<cdot>\<^sub>s (s j \<cdot>\<^sub>s f j)" and 
       g = "\<lambda>j. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> (s j)) \<cdot>\<^sub>s f j" in nsum_eq)
 apply (rule allI, rule impI,
        rule sc_mem, assumption, rule sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI,
        rule sc_mem,
        cut_tac sc_Ring,
        rule Ring.ring_tOp_closed, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule allI, rule impI,
        subst sc_assoc, assumption,
        cut_tac sc_Ring, 
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD, simp,
        simp,
    thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. r \<cdot>\<^sub>s (s j \<cdot>\<^sub>s f j)) n = 
                                \<Sigma>\<^sub>e M (\<lambda>j. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> s j) \<cdot>\<^sub>s f j) n",
    thin_tac "x = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n")

 apply (cut_tac n = n and f = "\<lambda>j. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> s j) \<cdot>\<^sub>s f j" and 
       g = "\<lambda>j. (\<lambda>x\<in>{j. j \<le> n}. r \<cdot>\<^sub>r\<^bsub>R\<^esub> (s x)) j \<cdot>\<^sub>s f j" in nsum_eq)
  apply (rule allI, rule impI,
        rule sc_mem,
        cut_tac sc_Ring,
        rule Ring.ring_tOp_closed, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
   apply (rule allI, rule impI,
         rule sc_mem, simp) apply (
          cut_tac sc_Ring,
        rule Ring.ring_tOp_closed, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
  apply (rule allI, rule impI)
         apply simp
  apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> n}. r \<cdot>\<^sub>r\<^bsub>R\<^esub> s x) \<in> {j. j \<le> n} \<rightarrow> A",
         blast)
  apply (rule Pi_I, simp)
apply (thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. (r \<cdot>\<^sub>r\<^bsub>R\<^esub> s j) \<cdot>\<^sub>s f j) n =
        \<Sigma>\<^sub>e M (\<lambda>j. (if j \<le> n then r \<cdot>\<^sub>r\<^bsub>R\<^esub> s j else undefined) \<cdot>\<^sub>s f j) n",
        cut_tac sc_Ring,
        rule Ring.ideal_ring_multiple, assumption+, simp add:Pi_def,
        assumption)
done
    
lemma (in Module) mem_single_l_spanTr:"\<lbrakk>ideal R A; h \<in> carrier M\<rbrakk> \<Longrightarrow>
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and>
      f \<in> {j. j \<le> n} \<rightarrow> {h} \<and> l_comb R M n s f \<in> linear_span R M A {h}
      \<longrightarrow> (\<exists>a \<in> A. l_comb R M n s f = a \<cdot>\<^sub>s h)"
apply (cut_tac sc_Ring)  
apply (induct_tac n)
 apply (rule impI, (erule conjE)+)
 apply (simp add:l_comb_def Ring.ideal_subset[of R A] bexI[of _ "s 0"])
apply (rule impI, (erule conjE)+,
       frule func_pre[of _ _ A], frule func_pre[of _ _ "{h}"],
       frule_tac n = n in l_comb_mem_linear_span[of A "{h}" s _ f],
       rule subsetI, simp, assumption+, simp,
       erule bexE)
apply (frule singleton_sub[of h "carrier M"])
 apply (frule Ring.ideal_subset1[of R A], assumption)
 apply (frule extend_fun[of s _ A "carrier R"], assumption)
 apply (frule_tac n = n in l_comb_Suc[of "{h}" A s _ f], assumption+,
        simp)
 apply (frule_tac A = "{j. j \<le> Suc n}" and x = "Suc n" in 
        funcset_mem[of f _ "{h}"], simp, simp,
        frule_tac A = "{j. j \<le> Suc n}" and x = "Suc n" in 
        funcset_mem[of s _ A], simp,
        frule_tac h = "s (Suc n)" in Ring.ideal_subset[of R A], assumption+)
 apply (frule_tac h = a in Ring.ideal_subset[of R A], assumption+,
        frule_tac h = "s (Suc n)" in Ring.ideal_subset[of R A], assumption+,
        simp add:sc_l_distr[THEN sym],
        frule_tac x = a and y = "s (Suc n)" in Ring.ideal_pOp_closed[of R A],
        assumption+, blast)
done

lemma (in Module) mem_single_l_span:"\<lbrakk>ideal R A; h \<in> carrier M; 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> n} \<rightarrow> {h}; 
       l_comb R M n s f \<in> linear_span R M A {h}\<rbrakk> \<Longrightarrow>
       \<exists>a \<in> A. l_comb R M n s f = a \<cdot>\<^sub>s h"
apply (simp add:mem_single_l_spanTr)
done

lemma (in Module) mem_single_l_span1:"\<lbrakk>ideal R A; h \<in> carrier M; 
       x \<in> linear_span R M A {h}\<rbrakk> \<Longrightarrow> \<exists>a \<in> A. x = a \<cdot>\<^sub>s h"
apply (simp add:linear_span_def, erule exE, (erule bexE)+, simp)
apply (frule_tac s = s and n = n and f = f in mem_single_l_span[of A h],
       assumption+)
apply (frule singleton_sub[of h "carrier M"],
      rule_tac s = s and f = f in l_comb_mem_linear_span[of A "{h}"],
      assumption+)
done

lemma (in Module) linear_span_subModule:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk>  \<Longrightarrow> 
                  submodule R M (linear_span R M A H)"
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:submodule_0)

apply (simp add:submodule_def)
apply (rule conjI)
 apply (simp add:linear_span_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (erule exE, (erule bexE)+)
 apply simp
 apply (simp add:l_comb_mem)
apply (rule conjI)
 apply (rule asubg_test) 
 apply (rule subsetI) apply (simp add:linear_span_def)
 apply (erule exE, (erule bexE)+)
 apply (simp add:l_comb_mem)
 apply (frule linear_span_inc_0[of A H], assumption, blast)
 apply (rule ballI)+
 apply (rule linear_span_pOp_closed, assumption+)
 apply (rule linear_span_iOp_closed, assumption+)
apply (rule allI)+
 apply (simp add:linear_span_sc_closed)
done

lemma (in Module) l_comb_mem_submoduleTr:"\<lbrakk>ideal R A; submodule R M N\<rbrakk> \<Longrightarrow>
 (s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> f \<in> {j. j \<le> n} \<rightarrow> carrier M \<and>
 (\<forall>j \<le> n.(s j) \<cdot>\<^sub>s (f j) \<in> N)) \<longrightarrow> l_comb R M n s f \<in> N"
apply (induct_tac n)
 apply (simp add:l_comb_def, rule impI, (erule conjE)+)
apply (frule func_pre[of _ _ A], frule func_pre[of _ _ "carrier M"], simp)
apply (simp add:l_comb_def)
apply (frule_tac a = "Suc n" in forall_spec, simp) 
apply (rule submodule_pOp_closed, assumption+)
done

lemma (in Module) l_span_sub_submodule:"\<lbrakk>ideal R A; submodule R M N; H \<subseteq> N\<rbrakk> \<Longrightarrow>
       linear_span R M A H \<subseteq> N"
apply (cut_tac sc_Ring)
 apply (rule subsetI, simp add:linear_span_def)
 apply (case_tac "H = {}", simp)
 apply (simp add:submodule_inc_0)

 apply simp
 apply (erule exE, (erule bexE)+)
 apply (cut_tac s = s and A = A and f = f and N = N and n = n in 
        l_comb_mem_submoduleTr, assumption+,
        frule submodule_subset[of N],
        frule subset_trans[of H N "carrier M"], assumption+,
        frule_tac f = f and A = "{j. j \<le> n}" and B = H and ?B1.0 = "carrier M"
        in extend_fun, assumption+)
 apply (subgoal_tac "\<forall>j\<le>n. s j \<cdot>\<^sub>s f j \<in> N", simp)
 apply (rule allI, rule impI)
 apply (rule submodule_sc_closed[of N], assumption,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
done

lemma (in Module) linear_span_sub:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk>  \<Longrightarrow> 
                  (linear_span R M A H) \<subseteq> carrier M"
apply (frule linear_span_subModule[of A H], assumption+)
apply (simp add:submodule_subset)
done

definition
  smodule_ideal_coeff :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme,
       'r set] \<Rightarrow> 'a set" where
  "smodule_ideal_coeff R M A = linear_span R M A (carrier M)"

abbreviation
  SMLIDEALCOEFF  ("(3_/ \<odot>\<^bsub>_\<^esub> _)" [64,64,65]64) where
  "A \<odot>\<^bsub>R\<^esub> M == smodule_ideal_coeff R M A"

lemma (in Module) smodule_ideal_coeff_is_Submodule:"ideal R A  \<Longrightarrow>
            submodule R M (A \<odot>\<^bsub>R\<^esub> M)"
apply (simp add:smodule_ideal_coeff_def)
apply (simp add:linear_span_subModule)
done

lemma (in Module) mem_smodule_ideal_coeff:"\<lbrakk>ideal R A; x \<in> A \<odot>\<^bsub>R\<^esub> M\<rbrakk> \<Longrightarrow>
             \<exists>n. \<exists>s \<in> {j. j \<le> n} \<rightarrow> A. \<exists>g \<in> {j. j \<le> n} \<rightarrow> carrier M.
              x = l_comb R M n s g" 
apply (cut_tac ag_inc_zero,
       frule nonempty[of "\<zero>" "carrier M"])
apply (simp add:smodule_ideal_coeff_def linear_span_def,
       erule exE, (erule bexE)+, blast)
done

definition
  quotient_of_submodules :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme,
            'a set, 'a set] \<Rightarrow> 'r set" where
  "quotient_of_submodules R M N P = {x | x. x\<in>carrier R \<and> 
                                    (linear_span R M (Rxa R x)  P) \<subseteq> N}"

definition
  Annihilator :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme]
    \<Rightarrow> 'r set" ("(Ann\<^bsub>_\<^esub> _)" [82,83]82) where
  "Ann\<^bsub>R\<^esub> M = quotient_of_submodules R M {\<zero>\<^bsub>M\<^esub>} (carrier M)"

abbreviation
  QOFSUBMDS  ("(4_ \<^bsub>_\<ddagger>_\<^esub> _)" [82,82,82,83]82) where
  "N \<^bsub>R\<ddagger>M\<^esub> P == quotient_of_submodules R M N P"

lemma (in Module) quotient_of_submodules_inc_0:
     "\<lbrakk>submodule R M P; submodule R M Q\<rbrakk> \<Longrightarrow> \<zero>\<^bsub>R\<^esub> \<in> (P \<^bsub>R\<ddagger>M\<^esub> Q)"
apply (simp add:quotient_of_submodules_def)
apply (cut_tac sc_Ring, simp add:Ring.ring_zero)
apply (simp add:linear_span_def)
 apply (frule submodule_inc_0[of Q], simp add:nonempty)
apply (rule subsetI)
 apply (simp, erule exE, (erule bexE)+)
 apply (simp, thin_tac "x = l_comb R M n s f", simp add:l_comb_def)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" in nsum_zeroA)
 apply (rule allI, rule impI,
       frule_tac x = j and f = s and A = "{j. j \<le> n}" in 
       funcset_mem[of _ _ "R \<diamondsuit>\<^sub>p \<zero>\<^bsub>R\<^esub>"], simp)
 apply (simp add:Rxa_def, erule bexE, simp) apply (
        simp add:Ring.ring_times_x_0,
        rule sc_0_m) apply (
        frule submodule_subset[of Q],
        simp add:Pi_def subsetD)
 apply (simp add:submodule_inc_0)
done
 
lemma (in Module) quotient_of_submodules_is_ideal:
      "\<lbrakk>submodule R M P; submodule R M Q\<rbrakk> \<Longrightarrow> ideal R (P \<^bsub>R\<ddagger>M\<^esub> Q)"
apply (frule quotient_of_submodules_inc_0 [of P Q], assumption+)
apply (cut_tac sc_Ring,
       rule Ring.ideal_condition[of R], assumption+)
apply (simp add:quotient_of_submodules_def)
apply (simp add:nonempty) apply (thin_tac "\<zero>\<^bsub>R\<^esub> \<in> P \<^bsub>R\<ddagger>M\<^esub> Q")
 apply (rule ballI)+
 apply (simp add:quotient_of_submodules_def) 
apply (erule conjE)+
 apply (rule conjI)
 apply (frule Ring.ring_is_ag,
        rule aGroup.ag_pOp_closed[of R], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
apply (subst linear_span_def)
 apply (frule submodule_inc_0 [of Q], simp add:nonempty)
 apply (rule subsetI, simp,
        erule exE, (erule bexE)+, simp add:l_comb_def,
        thin_tac "xa = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n")
 apply (cut_tac s = s and n = n and f = f in 
           l_comb_mem_submoduleTr[of "carrier R" P])
 apply (simp add:Ring.whole_ideal, assumption+)
 apply (frule Ring.ring_is_ag[of R],
        frule_tac x = y in aGroup.ag_mOp_closed[of R], assumption+,
        frule_tac x = x and y = "-\<^sub>a\<^bsub>R\<^esub> y" in aGroup.ag_pOp_closed, assumption+,
        frule_tac a = "x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y" in Ring.principal_ideal[of R], assumption+,
        frule_tac I = "R \<diamondsuit>\<^sub>p (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y)" in Ring.ideal_subset1, assumption+)
  apply (frule_tac f = s and A = "{j. j \<le> n}" and B = "R \<diamondsuit>\<^sub>p (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y)" 
         and ?B1.0 = "carrier R" in extend_fun, assumption+,
         frule_tac submodule_subset[of Q],
         frule_tac f = f and A = "{j. j \<le> n}" and B = Q  
         and ?B1.0 = "carrier M" in extend_fun, assumption+)        
  apply (subgoal_tac "\<forall>j\<le>n. s j \<cdot>\<^sub>s f j \<in> P", simp add:l_comb_def,
         thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and>
        f \<in> {j. j \<le> n} \<rightarrow> carrier M \<and> (\<forall>j\<le>n. s j \<cdot>\<^sub>s f j \<in> P) \<longrightarrow>
        l_comb R M n s f \<in> P",
         thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
         thin_tac "f \<in> {j. j \<le> n} \<rightarrow> carrier M")
  apply (rule allI, rule impI,
         frule_tac x = j and f = s and A = "{j. j \<le> n}" and 
         B = "R \<diamondsuit>\<^sub>p (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y)" in funcset_mem, simp, 
         thin_tac "s \<in> {j. j \<le> n} \<rightarrow> R \<diamondsuit>\<^sub>p (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y)",
         thin_tac "ideal R (R \<diamondsuit>\<^sub>p (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y))")
  apply (simp add:Rxa_def, fold Rxa_def, erule bexE, simp,
         thin_tac "s j = r \<cdot>\<^sub>r\<^bsub>R\<^esub> (x \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> y)")
  apply (simp add:Ring.ring_distrib1,
         frule_tac x = r and y = x in Ring.ring_tOp_closed, assumption+, 
         frule_tac x = r and y = "-\<^sub>a\<^bsub>R\<^esub> y" in Ring.ring_tOp_closed, assumption+,
         frule_tac x = j and A = "{j. j \<le> n}" and B = Q in funcset_mem,
         simp,
         frule_tac c = "f j" in subsetD[of Q "carrier M"], assumption+,
         simp add:sc_l_distr)
  apply (subst Ring.ring_inv1_2[THEN sym], assumption+,
         subst Ring.ring_inv1_1, assumption+)
  apply (frule_tac a = x in Ring.principal_ideal[of R], assumption+,
         frule_tac a = x in Ring.principal_ideal[of R], assumption+,
         frule_tac A = "R \<diamondsuit>\<^sub>p x" and H = Q and a = "r \<cdot>\<^sub>r\<^bsub>R\<^esub> x" and h = "f j" in
         sc_linear_span, assumption+, simp add:Rxa_def, blast,
         simp add:Pi_def)
  apply (frule_tac x = r in aGroup.ag_mOp_closed[of R], assumption+,
         frule_tac a = y in Ring.principal_ideal[of R], assumption+,
         frule_tac a = y in Ring.principal_ideal[of R], assumption+,
         frule_tac A = "R \<diamondsuit>\<^sub>p y" and H = Q and a = "(-\<^sub>a\<^bsub>R\<^esub> r) \<cdot>\<^sub>r\<^bsub>R\<^esub> y" and
         h = "f j" in sc_linear_span, assumption+, simp add:Rxa_def,
         blast,
         simp add:Pi_def)
  apply (frule_tac c = "(r \<cdot>\<^sub>r\<^bsub>R\<^esub> x) \<cdot>\<^sub>s f j" and A = "linear_span R M (R \<diamondsuit>\<^sub>p x) Q" 
         and B = P in subsetD, assumption+) apply (
         frule_tac c = "((-\<^sub>a\<^bsub>R\<^esub> r) \<cdot>\<^sub>r\<^bsub>R\<^esub> y) \<cdot>\<^sub>s f j" and 
         A = "linear_span R M (R \<diamondsuit>\<^sub>p y) Q" and B = P in subsetD, assumption+)
  apply (rule submodule_pOp_closed, assumption+)

  apply ((rule ballI)+,
         thin_tac "\<zero>\<^bsub>R\<^esub> \<in> P \<^bsub>R\<ddagger>M\<^esub> Q",
         simp add:quotient_of_submodules_def, erule conjE)
  apply (simp add:Ring.ring_tOp_closed)
  apply (rule subsetI)
  apply (frule submodule_inc_0[of Q],
         simp add:linear_span_def nonempty)
  apply (erule exE, (erule bexE)+)
  apply (rule_tac c = xa and A = "{xa. \<exists>n. \<exists>f\<in>{j. j \<le> n} \<rightarrow> Q.
                \<exists>s\<in>{j. j \<le> n} \<rightarrow> R \<diamondsuit>\<^sub>p x. xa = l_comb R M n s f}" in
          subsetD[of _ P], assumption+,
          thin_tac "{xa. \<exists>n. \<exists>f\<in>{j. j \<le> n} \<rightarrow> Q.
                \<exists>s\<in>{j. j \<le> n} \<rightarrow> R \<diamondsuit>\<^sub>p x. xa = l_comb R M n s f} \<subseteq> P")
  apply simp
  apply (frule_tac a = r and b = x in Ring.Rxa_mult_smaller[of R], assumption+)
  apply (frule_tac f = s and A = "{j. j \<le> n}" and B = "R \<diamondsuit>\<^sub>p (r \<cdot>\<^sub>r\<^bsub>R\<^esub> x)" and
          ?B1.0 = "R \<diamondsuit>\<^sub>p x" in extend_fun, assumption+)
  apply blast
done
 
lemma (in Module) Ann_is_ideal:"ideal R (Ann\<^bsub>R\<^esub> M)"
apply (simp add:Annihilator_def)
apply (rule quotient_of_submodules_is_ideal)
apply (simp add:submodule_0)
apply (simp add:submodule_whole)
done

lemma (in Module) linmap_im_of_lincombTr:"\<lbrakk>ideal R A; R module N; 
      f \<in> mHom R M N; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>  
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> g \<in> {j. j \<le> n} \<rightarrow> H \<longrightarrow>
      f (l_comb R M n s g) = l_comb R N n s (cmp f g)"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)
 apply (simp add:l_comb_def)
 apply (cut_tac m = "g 0" and f = f and a = "s 0" in mHom_lin [of N],
        assumption+,
        simp add:Pi_def subsetD, assumption,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset, simp add:cmp_def)

apply (rule impI, erule conjE)
 apply (frule_tac f = s in func_pre,
        frule_tac f = g in func_pre, simp)
 apply (simp add:l_comb_def)
 apply (subst mHom_add[of N f], assumption+)
 apply (rule nsum_mem,
        rule allI, rule impI, rule sc_mem,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
 apply (rule sc_mem,
         cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD, simp,
        frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" and f = s and 
                  B = A in funcset_mem, simp,
        cut_tac sc_Ring,
        frule_tac h = "s (Suc n)" in Ring.ideal_subset[of R A], assumption+,
        frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" and f = g and 
                  B = H in funcset_mem, simp,
        frule_tac c = "g (Suc n)" in subsetD[of H "carrier M"], assumption+)
 apply (simp add:mHom_lin cmp_def)
done
 
lemma (in Module) linmap_im_lincomb:"\<lbrakk>ideal R A; R module N; f \<in> mHom R M N; 
      H \<subseteq> carrier M; s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; g \<in> {j. j \<le> n} \<rightarrow> H \<rbrakk> \<Longrightarrow> 
      f (l_comb R M n s g) = l_comb R N n s (cmp f g)"
apply (simp add:linmap_im_of_lincombTr)
done

lemma (in Module) linmap_im_linspan:"\<lbrakk>ideal R A; R module N; f \<in> mHom R M N; 
       H \<subseteq> carrier M; s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; g \<in> {j. j \<le> n} \<rightarrow> H \<rbrakk> \<Longrightarrow> 
            f (l_comb R M n s g) \<in> linear_span R N A (f ` H)"
apply (frule l_comb_mem_linear_span[of A H s n g], assumption+) 
 apply (simp add:linmap_im_lincomb)
 apply (rule Module.l_comb_mem_linear_span[of N R A "f ` H" s n "cmp f g"],
        assumption+,
        rule subsetI,
        simp add:image_def, erule bexE, simp,
        frule_tac c = xa in subsetD[of H "carrier M"], assumption+,
        simp add:mHom_mem[of N f], assumption+)
 apply (rule Pi_I, simp add:cmp_def)
 apply (frule_tac f = g and A = "{j. j \<le> n}" and B = H and x = x in 
        funcset_mem, simp, simp add:image_def) 
 apply blast
done

lemma (in Module) linmap_im_linspan1:"\<lbrakk>ideal R A; R module N; f \<in> mHom R M N; 
      H \<subseteq> carrier M; h \<in> linear_span R M A H\<rbrakk> \<Longrightarrow> 
                              f h \<in> linear_span R N A (f ` H)"
apply (simp add:linear_span_def [of "R" "M"])
 apply (case_tac "H = {}", simp add:linear_span_def)
 apply (simp add:mHom_0, simp)
apply (erule exE, (erule bexE)+)
 apply (simp add:linmap_im_linspan)
done

(*
section "A module over two rings"

record ('a, 'r, 's) bModule = "'a aGroup" +
  sc_l  :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>\<^bsub>sl\<^esub>\<index>" 70)
  sc_r  :: "'a \<Rightarrow> 's \<Rightarrow> 'a"    (infixl "\<cdot>\<^bsub>sr\<^esub>\<index>" 70)

locale bModule = aGroup M +
  fixes R (structure)
  fixes S (structure)
  assumes  scl_Ring: "Ring R"
  and      scr_Ring: "Ring S" 
  and  scl_closed :
      "\<lbrakk> a \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow> a \<cdot>\<^bsub>sl\<^esub> m \<in> carrier M"
  and scr_closed :
      "\<lbrakk> b \<in> carrier S; m \<in> carrier M\<rbrakk> \<Longrightarrow> m \<cdot>\<^bsub>sr\<^esub> b \<in> carrier M" 
  and scl_l_distr:
      "\<lbrakk>a \<in> carrier R; b \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow>
       (a \<plusminus>\<^bsub>R\<^esub> b) \<cdot>\<^bsub>sl\<^esub> m = a \<cdot>\<^bsub>sl\<^esub> m \<plusminus> b \<cdot>\<^bsub>sl\<^esub> m"
  and scr_l_distr:
      "\<lbrakk>a \<in> carrier S; m \<in> carrier M; n \<in> carrier M \<rbrakk> \<Longrightarrow>
        (m \<plusminus> n) \<cdot>\<^bsub>sr\<^esub> a = m \<cdot>\<^bsub>sr\<^esub> a \<plusminus>  n \<cdot>\<^bsub>sr\<^esub> a"
  and scl_r_distr:
      "\<lbrakk> a \<in> carrier R; m \<in> carrier M; n \<in> carrier M \<rbrakk> \<Longrightarrow>
      a \<cdot>\<^bsub>sl\<^esub> (m \<plusminus> n) = a \<cdot>\<^bsub>sl\<^esub> m \<plusminus> a \<cdot>\<^bsub>sl\<^esub> n"
  and scr_r_distr:
        "\<lbrakk>a \<in> carrier S; b \<in> carrier S; m \<in> carrier M\<rbrakk> \<Longrightarrow>
          m \<cdot>\<^bsub>sr\<^esub> (a \<plusminus>\<^bsub>S\<^esub> b) = m \<cdot>\<^bsub>sr\<^esub> a \<plusminus>  m \<cdot>\<^bsub>sr\<^esub> b"
  and scl_assoc:
      "\<lbrakk> a \<in> carrier R; b \<in> carrier R; m \<in> carrier M \<rbrakk> \<Longrightarrow>
      (a \<cdot>\<^sub>r\<^bsub>R\<^esub> b) \<cdot>\<^bsub>sl\<^esub> m = a \<cdot>\<^bsub>sl\<^esub> (b \<cdot>\<^bsub>sl\<^esub> m)"
  and scr_assoc:
      "\<lbrakk>a \<in> carrier S; b \<in> carrier S; m \<in> carrier M \<rbrakk> \<Longrightarrow>
       m \<cdot>\<^bsub>sr\<^esub> (a \<cdot>\<^sub>r\<^bsub>S\<^esub> b)  =  (m \<cdot>\<^bsub>sr\<^esub> a) \<cdot>\<^bsub>sr\<^esub> b"
  and scl_one:
      "m \<in> carrier M \<Longrightarrow> (1\<^sub>r\<^bsub>R\<^esub>) \<cdot>\<^bsub>sl\<^esub> m = m" 
  and scr_one:
       "m \<in> carrier M \<Longrightarrow> m \<cdot>\<^bsub>sr\<^esub> (1\<^sub>r\<^bsub>S\<^esub>) = m" 

definition lModule :: "('a, 'r, 's, 'more) bModule_scheme \<Rightarrow> ('a, 'r) Module" where
       ("(_\<^sub>l)" [1000]999)
  "M\<^sub>l == \<lparr>carrier = carrier M, pop = pop M, mop = mop M, 
    zero = zero M, sprod = sc_l M \<rparr>"

definition scr_re :: "('a, 'b, 'c, 'more) bModule_scheme \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'a" where 
                  
 "scr_re M r m == sc_r M m r"

definition rModule :: "('a, 'r, 's, 'more) bModule_scheme \<Rightarrow> ('a, 's) Module" where
        ("(_\<^sub>r)" [1000]999) 
  "M\<^sub>r == \<lparr>carrier = carrier M, pop = pop M, mop = mop M, 
    zero = zero M, sprod = scr_re M \<rparr>"

lemma (in bModule) bmodule_is_ag:"aGroup M"  
apply assumption
done

lemma (in bModule) lModule_is_Module:"R module M\<^sub>l"
apply (subgoal_tac "aGroup M")
apply (rule Module.intro)
 apply (rule aGroup.intro)
 apply (simp add:lModule_def, simp add:aGroup.pop_closed[of M])
 apply (simp add:lModule_def, simp add:aGroup.ag_pOp_assoc)
 apply (simp add:lModule_def, simp add:aGroup.ag_pOp_commute)
 apply (simp add:lModule_def, rule mop_closed)
 apply (simp add:lModule_def, rule l_m, assumption+)
 apply (simp add:lModule_def, rule ex_zero)
 apply (simp add:lModule_def, rule l_zero, assumption)
apply (rule Module_axioms.intro)
 apply (simp add:scl_Ring)
 apply (simp add:lModule_def, rule  scl_closed, assumption+)
 apply (simp add:lModule_def, rule  scl_l_distr, assumption+)
 apply (simp add:lModule_def, rule  scl_r_distr, assumption+)
 apply (simp add:lModule_def, rule  scl_assoc, assumption+)
 apply (simp add:lModule_def, rule scl_one, assumption+)
done


lemma (in bModule) rModule_is_Module:"S module M\<^sub>r"
apply (subgoal_tac "aGroup M")
apply (rule Module.intro)
 apply (rule aGroup.intro)
 apply (simp add:rModule_def, simp add:aGroup.pop_closed[of M])
 apply (simp add:rModule_def, simp add:aGroup.ag_pOp_assoc)
 apply (simp add:rModule_def, simp add:aGroup.ag_pOp_commute)
 apply (simp add:rModule_def, rule mop_closed)
 apply (simp add:rModule_def, rule l_m, assumption+)
 apply (simp add:rModule_def, rule ex_zero)
 apply (simp add:rModule_def, rule l_zero, assumption)
apply (rule Module_axioms.intro,
       simp add:scr_Ring)
apply (simp add:rModule_def, simp add:scr_re_def scr_closed)
apply (simp add:rModule_def, simp add:scr_re_def, simp add:scr_r_distr)
apply (simp add:rModule_def, simp add:scr_re_def, rule scr_l_distr, 
        assumption+)
apply (simp add:rModule_def scr_re_def,
       subst scr_assoc[THEN sym], assumption+,
       cut_tac scr_Ring,
       simp add:Ring.ring_tOp_commute)
apply (simp add:rModule_def scr_re_def) 
apply (cut_tac m = m in scr_one, simp)
apply assumption+
done

lemma (in Module) sprodr_welldefTr1:"\<lbrakk>ideal R A; A \<subseteq> Ann\<^bsub>R\<^esub> M; a \<in> A;
       m \<in> carrier M\<rbrakk>  \<Longrightarrow> a \<cdot>\<^sub>s m = \<zero>" 
apply (simp add:Annihilator_def quotient_of_submodules_def)
apply (frule subsetD, assumption+)
 apply (simp add:CollectI, erule conjE, 
        thin_tac "A \<subseteq> {u \<in> carrier R.
                   linear_span R M (R \<diamondsuit>\<^sub>p u) (carrier M) \<subseteq> {\<zero>}}")
 apply (cut_tac sc_Ring,
        cut_tac a = a and A = "Rxa R a" in 
                         sc_linear_span[of  _ "carrier M" _ "m"],
                simp add:Ring.principal_ideal, simp, 
                simp add:Ring.a_in_principal, assumption)
 apply (frule subsetD[of "linear_span R M (R \<diamondsuit>\<^sub>p a) (carrier M)" "{\<zero>}"
                             "a \<cdot>\<^sub>s m"], assumption)
 apply simp
done

lemma (in Module) sprodr_welldefTr2:"\<lbrakk>ideal R A; A \<subseteq> Ann\<^bsub>R\<^esub> M; a \<in> carrier R; 
      x \<in> a \<uplus>\<^bsub>R\<^esub> A; m \<in> carrier M\<rbrakk>  \<Longrightarrow> a \<cdot>\<^sub>s m = x \<cdot>\<^sub>s m"
apply (cut_tac sc_Ring,
       frule Ring.mem_ar_coset1 [of R A a x], assumption+, erule bexE,
       rotate_tac -1, frule sym, thin_tac "h \<plusminus>\<^bsub>R\<^esub> a = x", simp)
apply (subst sc_l_distr)
 apply (simp add:Ring.ideal_subset, assumption+)
apply (simp add:sprodr_welldefTr1)
apply (frule sc_mem [of a m], assumption+)
apply (simp add:ag_l_zero)
done

definition cos_scr :: "[('r, 'm) Ring_scheme, 'r set, ('a, 'r, 'm1) Module_scheme] \<Rightarrow>
               'a \<Rightarrow> 'r set \<Rightarrow> 'a" where
  "cos_scr R A M == \<lambda>m. \<lambda>X. (SOME x. x \<in> X) \<cdot>\<^sub>s\<^bsub>M\<^esub> m"

lemma (in Module) cos_scr_welldef:"\<lbrakk>ideal R A; A \<subseteq> Ann\<^bsub>R\<^esub> M; a \<in> carrier R; 
       X = a \<uplus>\<^bsub>R\<^esub> A; m \<in> carrier M\<rbrakk>  \<Longrightarrow> cos_scr R A M m X = a \<cdot>\<^sub>s m" 
apply (cut_tac sc_Ring,
       frule Ring.a_in_ar_coset [of R A a], assumption+)
 apply (simp add:cos_scr_def,
        rule sprodr_welldefTr2[THEN sym], assumption+) 
 prefer 2 apply simp
apply (rule someI2_ex, blast, assumption)
done

definition r_qr_bmod :: "[('r, 'm) Ring_scheme, 'r set, ('a, 'r, 'm1) Module_scheme] \<Rightarrow> 
    ('a, 'r, 'r set) bModule" where 
 "r_qr_bmod R A M == \<lparr>carrier = carrier M, pop = pop M, mop = mop M, 
  zero = zero M, sc_l = sprod M, sc_r = cos_scr R A M \<rparr>" *)
 (* Remark. A should be an ideal contained in Ann\<^sub>R M. *)

definition
  faithful :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme]
                             \<Rightarrow> bool" where
  "faithful R M \<longleftrightarrow> Ann\<^bsub>R\<^esub> M = {\<zero>\<^bsub>R\<^esub>}"

section "nsum and Generators"

definition
  generator :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme,
               'a set] \<Rightarrow> bool" where
 "generator R M H == H \<subseteq> carrier M \<and> 
                      linear_span R M (carrier R) H = carrier M"

definition
  finite_generator :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme,
               'a set] \<Rightarrow> bool" where
  "finite_generator R M H \<longleftrightarrow> finite H \<and> generator R M H"

definition
  fGOver :: "[('a, 'r, 'm1) Module_scheme, ('r, 'm) Ring_scheme]  \<Rightarrow>  bool"
              (*(infixl 70)*)  where
  "fGOver M R \<longleftrightarrow> (\<exists>H. finite_generator R M H)"

abbreviation
  FGENOVER  (infixl "fgover" 70) where
  "M fgover R == fGOver M R"

lemma (in Module) h_in_linear_span:"\<lbrakk>H \<subseteq> carrier M; h \<in> H\<rbrakk> \<Longrightarrow>
                                   h \<in> linear_span R M (carrier R) H"
apply (subst sprod_one [THEN sym, of h])
 apply (simp add:subsetD)
 apply (cut_tac sc_Ring)
 apply (frule Ring.ring_one)
 apply (rule sc_linear_span [of "carrier R" "H" "1\<^sub>r\<^bsub>R\<^esub>" "h"])
 apply (simp add:Ring.whole_ideal) apply assumption+
done                                                   

lemma (in Module) generator_sub_carrier:"generator R M H \<Longrightarrow>
                                              H \<subseteq> carrier M" 
apply (simp add:generator_def)
done 

lemma (in Module) lin_span_sub_carrier:"\<lbrakk>ideal R A; 
       H \<subseteq> carrier M\<rbrakk> \<Longrightarrow> linear_span R M A H \<subseteq> carrier M"
apply (cut_tac sc_Ring)
apply (rule subsetI)
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}") apply simp
 apply (simp add:module_inc_zero) 
apply simp
apply (erule exE, (erule bexE)+, simp,
       thin_tac "x = l_comb R M n s f")
apply (simp add:l_comb_def) 
apply (rule_tac n = n in nsum_mem) 
 apply (rule allI, rule impI)
 apply (rule sc_mem)
 apply (simp add:Pi_def Ring.ideal_subset)
 apply (simp add:Pi_def subsetD)
done

lemma (in Module) lin_span_coeff_mono:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk>\<Longrightarrow>  
                        linear_span R M A H \<subseteq> linear_span R M (carrier R) H"
apply (cut_tac sc_Ring)
apply (rule subsetI)
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}") apply simp apply simp
 apply (erule exE, (erule bexE)+)
 apply (frule Ring.ideal_subset1 [of R A], assumption+)
apply (frule_tac  f = s in extend_fun, assumption+) 
 apply blast
done

lemma (in Module) l_span_sum_closedTr:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk>\<Longrightarrow> 
   \<forall>s. \<forall>f. s\<in>{j. j \<le> (n::nat)} \<rightarrow> A \<and> 
   f \<in> {j. j \<le> n} \<rightarrow> linear_span R M A H \<longrightarrow>
   (nsum M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n \<in> linear_span R M A H)"
apply (cut_tac sc_Ring)
apply (induct_tac n)
 apply ((rule allI)+, rule impI, simp) 
 apply (erule conjE)
 apply (rule linear_span_sc_closed, assumption+)
 apply (simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def)

apply ((rule allI)+, rule impI, erule conjE)
 apply (frule func_pre [of _ _ "A"],
        frule func_pre [of _ _ "linear_span R M A H"])
 apply (drule_tac x = s in spec,
        drule_tac x = f in spec)

 apply simp
 apply (rule linear_span_pOp_closed, assumption+)
 apply (rule linear_span_sc_closed, assumption+,
        simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def subsetD)
done

lemma (in Module) l_span_closed:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
 s \<in> {j. j \<le> (n::nat)} \<rightarrow> A;  f \<in> {j. j \<le> n} \<rightarrow> linear_span R M A H \<rbrakk> \<Longrightarrow>
 l_comb R M n s f \<in> linear_span R M A H"
apply (simp add:l_comb_def)
apply (simp add: l_span_sum_closedTr)
done 

lemma (in Module) l_span_closed1:"\<lbrakk>H \<subseteq> carrier M; 
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R;  
      f \<in> {j. j \<le> n} \<rightarrow> linear_span R M (carrier R) H \<rbrakk> \<Longrightarrow>
      \<Sigma>\<^sub>e M (\<lambda>j.  s j \<cdot>\<^sub>s (f j)) n \<in> linear_span R M (carrier R) H"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal [of "R"])
apply (frule l_span_sum_closedTr[of "carrier R" H n], assumption+)
apply (drule_tac x = s in spec,
       drule_tac x = f in spec,
       simp)
done

lemma (in Module) l_span_closed2Tr0:"\<lbrakk>ideal R A; H \<subseteq> carrier M; Ring R; s \<in> A;
     f \<in> linear_span R M (carrier R) H \<rbrakk> \<Longrightarrow> s \<cdot>\<^sub>s f \<in> linear_span R M A H"
apply (cut_tac sc_Ring)
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (rule sc_a_0,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset) 

 apply (simp add:linear_span_def) 
 apply (erule exE, (erule bexE)+, simp,
        thin_tac "f = l_comb R M n sa fa")
 apply (frule Ring.whole_ideal[of R])
 apply (frule_tac h = s in Ring.ideal_subset[of R A], assumption+)
 apply (frule_tac s = sa and g = f in l_comb_sc1[of "carrier R" H s],
        assumption+, simp add:l_comb_def,
        thin_tac "s \<cdot>\<^sub>s \<Sigma>\<^sub>e M (\<lambda>k. sa k \<cdot>\<^sub>s f k) n = 
                                    \<Sigma>\<^sub>e M (\<lambda>k. (s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa k) \<cdot>\<^sub>s f k) n")
 apply (cut_tac n = n and f = "\<lambda>j. (s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa j) \<cdot>\<^sub>s f j" and 
        g = "\<lambda>j. ((\<lambda>x\<in>{j. j \<le> n}. (s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa x)) j) \<cdot>\<^sub>s f j" in nsum_eq)
        apply (rule allI, rule impI, rule sc_mem,
               rule Ring.ring_tOp_closed, assumption+,
               simp add:Pi_def,
               simp add:Pi_def subsetD)
        apply (rule allI, rule impI, simp,
                rule sc_mem,
               rule Ring.ring_tOp_closed, assumption+,
               simp add:Pi_def,
               simp add:Pi_def subsetD)
        apply (rule allI, rule impI, simp)
 apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> n}. (s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa x)) \<in> {j. j \<le> n} \<rightarrow> A",
        blast,
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. (s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa j) \<cdot>\<^sub>s f j) n =
        \<Sigma>\<^sub>e M (\<lambda>j. (\<lambda>x\<in>{j. j \<le> n}. s \<cdot>\<^sub>r\<^bsub>R\<^esub> sa x) j \<cdot>\<^sub>s f j) n")
        apply (rule Pi_I, simp,
               rule_tac x = s and r = "sa x" in 
               Ring.ideal_ring_multiple1[of R A], assumption+)
               apply (simp add:Pi_def)
done

lemma (in Module) l_span_closed2Tr:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow> 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> 
       f \<in> {j. j \<le> n} \<rightarrow> linear_span R M (carrier R) H \<longrightarrow>
            l_comb R M n s f \<in> linear_span R M A H"
apply (cut_tac sc_Ring)
apply (induct_tac n)
apply (rule impI, (erule conjE)+)
apply (case_tac "H = {}")
 apply (simp add:linear_span_def)
 apply (simp add:l_comb_def)
 apply (rule sc_a_0,
        cut_tac sc_Ring,
        simp add:Pi_def Ring.ideal_subset) 
 apply (simp add:l_comb_def l_span_closed2Tr0)

apply (rule impI, erule conjE,
       frule func_pre[of s], frule func_pre[of f], simp)
 apply (simp add:l_comb_def) 
 apply (rule linear_span_pOp_closed, assumption+) 
 apply (rule_tac s = "s (Suc n)" and f = "f (Suc n)" in 
                 l_span_closed2Tr0[of A H], assumption+,
       (simp add:Pi_def)+)
done

lemma (in Module) l_span_closed2:"\<lbrakk>ideal R A; H \<subseteq> carrier M;
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A ; 
       f \<in> {j. j \<le> n} \<rightarrow> linear_span R M (carrier R) H\<rbrakk> \<Longrightarrow>
       l_comb R M n s f \<in> linear_span R M A H"
apply (simp add:l_span_closed2Tr)
done

lemma (in Module) l_span_l_span:"H \<subseteq> carrier M \<Longrightarrow>
       linear_span R M (carrier R) (linear_span R M (carrier R) H) =
                                          linear_span R M (carrier R) H"
apply (cut_tac sc_Ring, frule Ring.whole_ideal[of R])
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule linear_span_inc_0[of "carrier R" H], assumption+,
        frule nonempty[of _ "linear_span R M (carrier R) H"],
        simp add:linear_span_def[of R M "carrier R" 
                            "linear_span R M (carrier R) H"],
        erule exE, (erule bexE)+, simp)
 apply (frule_tac s = s and n = n and f = f in l_span_closed2[of "carrier R"],
        assumption+,
        frule lin_span_sub_carrier[of "carrier R" "H"], assumption+,
        rule subsetI)
 apply (rule_tac h = x in h_in_linear_span[of "linear_span R M (carrier R) H"],
        assumption+)
done

lemma (in Module) l_spanA_l_span:"\<lbrakk>ideal R A; H \<subseteq> carrier M\<rbrakk> \<Longrightarrow>
       linear_span R M A (linear_span R M (carrier R) H) =
                                          linear_span R M A H"
apply (cut_tac sc_Ring, frule Ring.whole_ideal[of R])
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule linear_span_inc_0[of "carrier R" H], assumption+,
        frule nonempty[of _ "linear_span R M (carrier R) H"],
        simp add:linear_span_def[of R M A 
                            "linear_span R M (carrier R) H"],
        erule exE, (erule bexE)+, simp)
 apply (frule_tac s = s and n = n and f = f in l_span_closed2[of A],
        assumption+)
 apply (frule l_span_cont_H[of H])
 apply (frule l_span_gen_mono[of "H" "linear_span R M (carrier R) H" A],
        simp add:lin_span_sub_carrier[of "carrier R" H], assumption)
 apply assumption
done 

lemma (in Module) l_span_zero:"ideal R A \<Longrightarrow> linear_span R M A {\<zero>} = {\<zero>}"
apply (cut_tac sc_Ring)
apply (rule equalityI)
 apply (rule subsetI,
        frule_tac x = x in mem_single_l_span1[of A \<zero>],
        simp add:ag_inc_zero, assumption,
        erule bexE, frule_tac h = a in Ring.ideal_subset[of R A], assumption+,
        simp add:sc_a_0)
 apply (rule subsetI, simp, rule linear_span_inc_0, assumption,
        rule subsetI, simp add:ag_inc_zero)
done

lemma (in Module) l_span_closed3:"\<lbrakk>ideal R A; generator R M H;
       A \<odot>\<^bsub>R\<^esub> M = carrier M\<rbrakk> \<Longrightarrow> linear_span R M A H = carrier M"
apply (cut_tac sc_Ring)

apply (rule equalityI) 
 apply (cut_tac linear_span_subModule[of A H],
        simp add:submodule_subset, assumption,
        simp add:generator_def)

apply (rule subsetI) 
 apply (simp add:generator_def)
 apply (erule conjE) 
 apply (case_tac "H = {}", simp, simp add:linear_span_def)
apply (simp add:smodule_ideal_coeff_def)
 apply (rotate_tac -2, frule sym,
        thin_tac "linear_span R M (carrier R) H = carrier M")
 apply simp 
 apply (frule sym, 
        thin_tac "linear_span R M A (linear_span R M (carrier R) H) =
                  linear_span R M (carrier R) H")
 apply (frule_tac a = x in eq_set_inc[of _ "linear_span R M (carrier R) H"
        "linear_span R M A (linear_span R M (carrier R) H)"], assumption+,
        thin_tac "x \<in> linear_span R M (carrier R) H",
        thin_tac "linear_span R M (carrier R) H =
         linear_span R M A (linear_span R M (carrier R) H)")
 apply (frule sym, 
        thin_tac "carrier M = linear_span R M (carrier R) H",
        frule subset_trans[of H "linear_span R M (carrier R) H" "carrier M"],
        simp,
        thin_tac "linear_span R M (carrier R) H = carrier M")
 apply (frule Ring.whole_ideal,
        frule linear_span_inc_0 [of "carrier R" "H"], assumption+,
        frule nonempty [of "\<zero>" "linear_span R M (carrier R) H"])
apply (simp add:linear_span_def [of _ _ _ "linear_span R M (carrier R) H"])
 apply (erule exE, (erule bexE)+)
apply (simp add:l_span_closed2) 
done

lemma (in Module) generator_generator:"\<lbrakk>generator R M H; H1 \<subseteq> carrier M; 
           H \<subseteq> linear_span R M (carrier R) H1\<rbrakk>  \<Longrightarrow>  generator R M H1"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal[of R],
       frule linear_span_subModule[of "carrier R" H1], assumption,
       frule l_span_sub_submodule[of "carrier R" 
            "linear_span R M (carrier R) H1" H], assumption+)
apply (simp add:generator_def)
apply (rule equalityI,
       simp add:submodule_subset, assumption)
done

lemma (in Module) generator_elimTr:
"f \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier M \<and> generator R M (f ` {j. j \<le> n}) \<and> 
(\<forall>i\<in>nset (Suc 0) n. f i \<in> 
   linear_span R M (carrier R) (f ` {j. j \<le> (i - Suc 0)})) \<longrightarrow> 
 linear_span R M (carrier R) {f 0} = carrier M"
apply (induct_tac n)
 apply (rule impI, (erule conjE)+)
 apply (simp add:nset_def generator_def)

apply (rule impI)
 apply (erule conjE)+
 apply (frule func_pre [of _ _ "carrier M"], simp)
 apply (subgoal_tac "generator R M (f ` {j. j \<le> n})")
 apply (subgoal_tac "\<forall>i\<in>nset (Suc 0) n.
         f i \<in> linear_span R M (carrier R) (f ` {j. j \<le> (i - Suc 0)})")
 apply simp
 apply (thin_tac "generator R M (f ` {j. j \<le> n}) \<and>
     (\<forall>i\<in>nset (Suc 0) n. f i \<in> linear_span R M (carrier R) 
              (f ` {j. j \<le> i - Suc 0})) \<longrightarrow>
         linear_span R M (carrier R) {f 0} = carrier M")
 apply (rule ballI)
 apply (frule_tac x = i in bspec, simp add:nset_def, assumption)
 apply (thin_tac "generator R M (f ` {j. j \<le> n}) \<and>
         (\<forall>i\<in>nset (Suc 0) n.
         f i \<in> linear_span R M (carrier R) (f ` {j. j \<le> i - Suc 0})) \<longrightarrow>
         linear_span R M (carrier R) {f 0} = carrier M")
 apply (frule_tac x = "Suc n" in bspec, simp add:nset_def,
        thin_tac "\<forall>i\<in>nset (Suc 0) (Suc n).
            f i \<in> linear_span R M (carrier R) (f ` {j. j \<le> i - Suc 0})",
        simp)
 apply (subgoal_tac "f ` {j. j \<le> Suc n} \<subseteq> linear_span R M (carrier R) (f ` {j. j \<le> n})")
 apply (frule_tac H = "f ` {j. j \<le> Suc n}" and ?H1.0 = "f ` {j. j \<le> n}"
        in generator_generator,
        rule subsetI, simp add:image_def, erule exE, erule conjE, simp,
        simp add:Pi_def)
 apply assumption+
 apply (rule subsetI, simp add:image_def, erule exE, erule conjE)
 apply (case_tac "xa = Suc n", simp)
 apply (frule_tac m = xa and n = "Suc n" in noteq_le_less, assumption,
        thin_tac "xa \<le> Suc n",
        frule_tac x = xa and n = "Suc n" in less_le_diff, 
        thin_tac "xa < Suc n", simp)
 apply (rule_tac H = "{y. \<exists>x\<le>n. y = f x}" and h = "f xa" in 
                       h_in_linear_span,
        rule subsetI, simp add:image_def, erule exE, erule conjE,
        simp add:Pi_def)
 apply (simp, blast)
done

lemma (in Module) generator_generator_elim:
 "\<lbrakk>f \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier M; generator R M (f ` {j. j \<le> n}); 
  (\<forall>i\<in>nset (Suc 0) n. f i \<in> linear_span R M (carrier R) 
     (f ` {j. j \<le> (i - Suc 0)}))\<rbrakk> \<Longrightarrow> 
   linear_span R M (carrier R) {f 0} = carrier M"
apply (simp add:generator_elimTr [of f n])
done

lemma (in Module) surjec_generator:"\<lbrakk>R module N; f \<in> mHom R M N;
 surjec\<^bsub>M,N\<^esub> f; generator R M H\<rbrakk> \<Longrightarrow> generator R N (f ` H)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
apply (simp add:generator_def, erule conjE)
 apply (simp add:surjec_def, (erule conjE)+)
 apply (simp add:aHom_def, (erule conjE)+)
 apply (simp add:image_sub [of "f" "carrier M" "carrier N" "H"])

apply (frule Module.lin_span_sub_carrier[of N R "carrier R" "f ` H"],
       assumption,
       simp add:image_sub [of "f" "carrier M" "carrier N" "H"])
apply (rule equalityI, assumption+)
 apply (rule subsetI)
 apply (simp add:surj_to_def,
        thin_tac "f \<in> extensional (carrier M)",
        thin_tac "\<forall>a\<in>carrier M. \<forall>b\<in>carrier M. f (a \<plusminus> b) = f a \<plusminus>\<^bsub>N\<^esub> f b")
 apply (frule sym, rotate_tac 6, frule sym,
        thin_tac "f ` carrier M = carrier N",
        frule_tac a = x and A = "carrier N" and B = "f ` carrier M" in
        eq_set_inc, assumption,
        thin_tac "carrier N = f ` carrier M", 
        thin_tac "carrier M = linear_span R M (carrier R) H")
 apply (simp add:image_def[of f "carrier M"], erule bexE)
 apply (frule sym, thin_tac "linear_span R M (carrier R) H = carrier M",
        frule_tac a = xa in eq_set_inc[of _ "carrier M" 
        "linear_span R M (carrier R) H"], assumption,
        thin_tac "carrier M = linear_span R M (carrier R) H",
        thin_tac "linear_span R N (carrier R) (f ` H) \<subseteq> carrier N")

 apply (simp add:linear_span_def)
apply (case_tac "H = {}", simp) 
 apply (simp add:mHom_0, simp,
        erule exE, (erule bexE)+)
 apply (cut_tac sc_Ring, frule Ring.whole_ideal[of R],
       frule_tac s = s and n = n and g = fa in 
       linmap_im_linspan[of "carrier R" N f H], assumption+,
       rotate_tac -5, frule sym,
       thin_tac "xa = l_comb R M n s fa", simp,
       thin_tac "l_comb R M n s fa = xa")
 apply (simp add:linear_span_def)
done   

lemma (in Module) surjec_finitely_gen:"\<lbrakk>R module N; f \<in> mHom R M N;
       surjec\<^bsub>M,N\<^esub> f; M fgover R\<rbrakk>  \<Longrightarrow> N fgover R"
apply (simp add:fGOver_def)
 apply (erule exE)
 apply (simp add:finite_generator_def [of "R" "M"],erule conjE)
 apply (frule_tac H = H in surjec_generator[of N f], assumption+)
apply (simp add:finite_generator_def [of "R" "N"])
 apply (frule_tac F = H and h = f in finite_imageI)  
 apply blast
done
    
subsection "Sum up coefficients" 
 text\<open>Symbolic calculation.\<close>    

lemma (in Module) similar_termTr:"\<lbrakk>ideal R A; a \<in> A\<rbrakk> \<Longrightarrow>
 \<forall>s. \<forall>f. s \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<and> 
         f \<in> {j. j \<le> n} \<rightarrow> carrier M \<and> 
         m \<in> f ` {j. j \<le> n} \<longrightarrow>
       (\<exists>t\<in>{j. j \<le> n} \<rightarrow> A. nsum M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n \<plusminus> a \<cdot>\<^sub>s m = 
           nsum M (\<lambda>j. t j \<cdot>\<^sub>s (f j)) n )"
apply (cut_tac sc_Ring)   
apply (induct_tac n)
 apply (rule allI)+ apply (rule impI) apply (erule conjE)+
 apply simp
 apply (rule_tac x = "\<lambda>k\<in>{0::nat}. (s 0 \<plusminus>\<^bsub>R\<^esub> a)" in bexI)
 apply (simp add: Ring.ideal_subset sc_l_distr)
 apply simp
   apply (simp add:Ring.ideal_pOp_closed)

(** n **)
apply ((rule allI)+, rule impI, (erule conjE)+)
 apply (simp del:nsum_suc add:image_def)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" in nsum_mem,
        rule allI, rule impI, rule sc_mem,
        simp add:funcset_mem Ring.ideal_subset,
        simp add:funcset_mem,
        frule_tac x = "Suc n" and f = s and A = "{j. j \<le> Suc n}" and
        B = A in funcset_mem, simp,
        frule_tac h = "s (Suc n)" in Ring.ideal_subset, assumption+,
        frule_tac x = "Suc n" and f = f and A = "{j. j \<le> Suc n}" and
        B = "carrier M" in funcset_mem, simp,
        frule_tac a = "s (Suc n)" and m = "f (Suc n)" in sc_mem, assumption+,
        cut_tac a = a and m = m in sc_mem,
        simp add:Ring.ideal_subset, erule exE, simp add:Pi_def,
        erule exE, erule conjE)
 apply (case_tac "x = Suc n", simp)  (***** case x = Suc n ********)
 apply (subst ag_pOp_assoc, assumption+)
 apply (thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<in> carrier M",
        thin_tac "s (Suc n) \<cdot>\<^sub>s f (Suc n) \<in> carrier M",
        thin_tac "a \<cdot>\<^sub>s f (Suc n) \<in> carrier M",
        thin_tac "\<forall>s fa.
           s \<in> {j. j \<le> n} \<rightarrow> A \<and>
           fa \<in> {j. j \<le> n} \<rightarrow> carrier M \<and> (\<exists>x\<le>n. f (Suc n) = fa x) \<longrightarrow>
           (\<exists>t\<in>{j. j \<le> n} \<rightarrow> A.
               \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s fa j) n \<plusminus> a \<cdot>\<^sub>s f (Suc n) =
               \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s fa j) n)")
 apply (subst sc_l_distr[THEN sym], assumption+,
        simp add:Ring.ideal_subset, assumption+)
 apply (frule func_pre[of _ _ A],
        frule_tac f = s and n = n and g = "\<lambda>k\<in>{0::nat}. (s (Suc n) \<plusminus>\<^bsub>R\<^esub> a)" and
        m = 0 and A = A and B = A in jointfun_hom0,
        simp add: Ring.ideal_pOp_closed)
 apply (subgoal_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> (s (Suc n) \<plusminus>\<^bsub>R\<^esub> a) \<cdot>\<^sub>s f (Suc n) =
      \<Sigma>\<^sub>e M (\<lambda>j. (jointfun n s 0 (\<lambda>k\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> a)) j \<cdot>\<^sub>s f j) (Suc n)",
      simp,
      thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> (s (Suc n) \<plusminus>\<^bsub>R\<^esub> a) \<cdot>\<^sub>s f (Suc n) =
      \<Sigma>\<^sub>e M (\<lambda>j. jointfun n s 0 (\<lambda>k\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> a) j \<cdot>\<^sub>s f j) n \<plusminus>
      jointfun n s 0 (\<lambda>k\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> a) (Suc n) \<cdot>\<^sub>s f (Suc n)")
 apply blast
 apply simp
 apply (simp add:jointfun_def sliden_def)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" and g = "\<lambda>j. (if j \<le> n then s j
        else (\<lambda>k\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> a) (sliden (Suc n) j)) \<cdot>\<^sub>s f j" in
        nsum_eq)
        apply (rule allI, rule impI, rule sc_mem,
               simp add:Pi_def Ring.ideal_subset,
               simp add:Pi_def)
        apply (rule allI, rule impI, simp, rule sc_mem,
               simp add:Pi_def Ring.ideal_subset,
               simp add:Pi_def)
        apply (rule allI, rule impI, simp)
  apply simp
  
  apply (frule_tac m = x and n = "Suc n" in noteq_le_less, assumption,
         thin_tac "x \<le> Suc n",
         frule_tac x = x and n = "Suc n" in less_le_diff,
         thin_tac "x < Suc n", simp)
  apply (frule func_pre[of _ _ A], frule func_pre[of _ _ "carrier M"])
  apply (drule_tac x = s in spec,
         drule_tac x = f in spec)
   apply (subgoal_tac "\<exists>xa\<le>n. f x = f xa", simp,
          thin_tac "\<exists>xa\<le>n. f x = f xa", erule bexE)
   apply (subst ag_pOp_assoc, assumption+,
          frule_tac x = "s (Suc n) \<cdot>\<^sub>s f (Suc n)" and y = "a \<cdot>\<^sub>s f x" in 
          ag_pOp_commute, assumption+, simp,
          thin_tac "s (Suc n) \<cdot>\<^sub>s f (Suc n) \<plusminus> a \<cdot>\<^sub>s f x =
          a \<cdot>\<^sub>s f x \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n)",
          subst ag_pOp_assoc[THEN sym], assumption+, simp,
    thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n \<plusminus> a \<cdot>\<^sub>s f x = \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n")
  apply (frule_tac f = t and n = n and g = "\<lambda>k\<in>{0::nat}. s (Suc n)" and
         m = 0 and A = A and B = A in jointfun_hom0,
         simp, simp)
  apply (subgoal_tac "\<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) =
         \<Sigma>\<^sub>e M (\<lambda>j. (jointfun n t 0 (\<lambda>k\<in>{0}. s (Suc n))) j \<cdot>\<^sub>s f j) (Suc n)",
         simp,
         thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s f j) n \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun n t 0 (\<lambda>k\<in>{0}. s (Suc n)) j \<cdot>\<^sub>s f j) n \<plusminus>
        jointfun n t 0 (\<lambda>k\<in>{0}. s (Suc n)) (Suc n) \<cdot>\<^sub>s f (Suc n)")
  apply blast
   apply (simp add:jointfun_def sliden_def)
   apply (cut_tac n = n and f = "\<lambda>j. t j \<cdot>\<^sub>s f j" and 
          g = "\<lambda>j. (if j \<le> n then t j  else (\<lambda>k\<in>{0}. s (Suc n)) 
                (sliden (Suc n) j)) \<cdot>\<^sub>s f j" in nsum_eq)
   apply (rule allI, rule impI, rule sc_mem,
          simp add:Pi_def Ring.ideal_subset,
          simp add:Pi_def)
   apply (rule allI, rule impI, simp, rule sc_mem,
          simp add:Pi_def Ring.ideal_subset,
          simp add:Pi_def)   
   apply (rule allI, rule impI, simp, simp)
   apply blast
done

lemma (in Module) similar_term1:"\<lbrakk>ideal R A; a \<in> A; s \<in> {j. j\<le>(n::nat)} \<rightarrow> A;
       f \<in> {j. j \<le> n} \<rightarrow> carrier M; m \<in> f ` {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
      \<exists>t\<in>{j. j \<le> n} \<rightarrow> A. \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n \<plusminus> a \<cdot>\<^sub>s m =
             \<Sigma>\<^sub>e M (\<lambda>j.  t j \<cdot>\<^sub>s (f j)) n" 
apply (simp add:similar_termTr)
done


lemma (in Module) same_togetherTr:"\<lbrakk>ideal R A; H \<subseteq> carrier M \<rbrakk> \<Longrightarrow> 
 \<forall>s. \<forall>f. s\<in>{j. j \<le> (n::nat)} \<rightarrow> A  \<and> f \<in> {j. j \<le> n} \<rightarrow> H \<longrightarrow> 
 (\<exists>t \<in> {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} \<rightarrow> A. 
  \<exists>g \<in> {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} \<rightarrow> f ` {j. j \<le> n}. 
   surj_to g {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} (f ` {j. j \<le> n}) \<and> 
  nsum M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n = nsum M (\<lambda>k. t k \<cdot>\<^sub>s (g k)) 
       (card (f ` {j. j \<le> n}) - Suc 0))"  
apply (induct_tac n)
 apply ((rule allI)+, rule impI, erule conjE)
 apply (simp del: Pi_split_insert_domain)
 apply (frule_tac f = f and A = "{0}" and B= H in func_to_img,
        frule_tac f = f and A = "{0}" and B= H in surj_to_image,
        fastforce simp add:image_def)

apply ((rule allI)+, rule impI, erule conjE)
 apply (frule func_pre [of _ _ "A"], frule func_pre [of _ _ "H"])
 apply (drule_tac x = s in spec,
        drule_tac x = f in spec,
        simp, (erule bexE)+ , (erule conjE)+, simp,
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n =
        \<Sigma>\<^sub>e M (\<lambda>k. t k \<cdot>\<^sub>s g k) (card (f ` {j. j \<le> n}) - Suc 0)")

apply (case_tac "f (Suc n) \<in> f ` {j. j \<le> n}")
 apply (frule_tac a = "s (Suc n)" and s = t and 
        n = "card (f ` {j. j \<le> n}) - Suc 0" and f = g and m = "f (Suc n)" in 
        similar_term1[of A],
        simp add:Pi_def,
        assumption,
        frule_tac f = f and A = "{j. j \<le> n}" and B = H in image_sub0,
        frule_tac A = "f ` {j. j \<le> n}" and B = H and C = "carrier M" 
         in subset_trans, assumption,
        rule_tac f = g and A = "{j. j \<le> card (f ` {j. j \<le> n}) - Suc 0}" and 
                 B = "f ` {j. j \<le> n}" and ?B1.0 = "carrier M" in extend_fun, 
        assumption+)
        apply (simp add:surj_to_def)
  apply (erule bexE, simp,
         thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s g j) (card (f ` {j. j \<le> n}) - Suc 0) \<plusminus>
        s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        \<Sigma>\<^sub>e M (\<lambda>j. ta j \<cdot>\<^sub>s g j) (card (f ` {j. j \<le> n}) - Suc 0)") 
  apply (simp add:Nset_img0)
  apply blast
  
  apply (frule_tac f = t and n = "card (f ` {j. j \<le> n}) - Suc 0" and A = A and
        g = "\<lambda>k\<in>{0::nat}. s (Suc n)" and m = 0 and B = A in jointfun_hom0)
        apply (simp add:Pi_def,
               simp)
  apply (frule_tac f = g and n = "card (f ` {j. j \<le> n}) - Suc 0" and 
         A = "f ` {j. j \<le> n}" and g = "\<lambda>k\<in>{0::nat}. f (Suc n)" and m = 0 and 
         B = "{f (Suc n)}" in jointfun_hom0)
        apply (simp add:Pi_def,
               simp)
  apply (subgoal_tac "\<Sigma>\<^sub>e M (\<lambda>k. t k \<cdot>\<^sub>s g k) (card (f ` {j. j \<le> n}) - Suc 0) \<plusminus>
                s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        \<Sigma>\<^sub>e M (\<lambda>j. (jointfun (card (f ` {j. j \<le> n}) - Suc 0) t 0 (\<lambda>k\<in>{0}. 
            s (Suc n))) j \<cdot>\<^sub>s (jointfun (card (f ` {j. j \<le> n}) - Suc 0) g 0 
        (\<lambda>k\<in>{0}. f (Suc n))) j) (card (f ` {j. j \<le> (Suc n)}) - Suc 0)", simp, 
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>k. t k \<cdot>\<^sub>s g k) (card (f ` {j. j \<le> n}) - Suc 0) \<plusminus>
        s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun (card (f ` {j. j \<le> n}) - Suc 0) t 0
                   (\<lambda>k\<in>{0}. s (Suc n)) j \<cdot>\<^sub>s
                  jointfun (card (f ` {j. j \<le> n}) - Suc 0) g 0
                   (\<lambda>k\<in>{0}. f (Suc n))
                   j) (card (f ` {j. j \<le> Suc n}) - Suc 0)")
  apply (simp del:nsum_suc add:card_image_Nsetn_Suc)
  apply (simp del:nsum_suc add:image_Nset_Suc[THEN sym])
 apply (subgoal_tac "surj_to (jointfun (card (f ` {j. j \<le> n}) - Suc 0) g 0 
       (\<lambda>k\<in>{0}. f (Suc n))) {l. l \<le> Suc (card (f ` {j. j \<le> n}) - Suc 0)} 
       (f ` {j. j \<le> Suc n})", blast)

   apply (simp add:surj_to_def)
   apply (frule_tac f = g and n = "card (f ` {j. j \<le> n}) - Suc 0" and A = "f ` {j. j \<le> n}" and g = "\<lambda>k\<in>{0}. f (Suc n)" and m = 0 and B = "{f (Suc n)}" in
  im_jointfun)
   apply (simp add:Pi_def)
   apply simp
   apply (simp add:image_Nset_Suc[THEN sym])
   apply (simp add:card_image_Nsetn_Suc)
   apply (simp add:Nset_img)

   apply (frule_tac f = f and A = "{j. j \<le> Suc n}" and B = H in image_sub0)
   apply (frule_tac A = "f ` {j. j \<le> Suc n}" and B = H and C = "carrier M" in
          subset_trans, assumption+)
   apply (cut_tac H = H and s = t and n = "card (f ` {j. j \<le> n}) - Suc 0" 
         and f = g and t = "\<lambda>k\<in>{0}. s (Suc n)" and m = 0 and 
         g = "\<lambda>k\<in>{0}. f (Suc n)" in 
         l_comb_jointfun_jj[of _ A], assumption+) 
   apply (frule_tac f = f and A = "{j. j \<le> n}" and B = H in image_sub0)
   apply (rule_tac f = g and A = "{j. j \<le> card (f ` {j. j \<le> n}) - Suc 0}" and
          B = "f ` {j. j \<le> n}" in extend_fun[of _ _ _ H], assumption+,
          simp add:Pi_def, simp add:Pi_def)
   apply simp
   apply (simp add:jointfun_def sliden_def)
done

 (* H shall a generator *)
lemma (in Module) same_together:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
       s \<in> {j. j \<le> (n::nat)} \<rightarrow> A; f \<in> {j. j \<le> n} \<rightarrow> H\<rbrakk> \<Longrightarrow> 
 \<exists>t \<in> {j. j \<le> (card (f ` {j. j \<le> (n::nat)}) - Suc 0)} \<rightarrow> A. 
 \<exists>g \<in> {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} \<rightarrow> f ` {j. j \<le> n}. 
       surj_to g {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} (f ` {j. j \<le> n}) \<and> 
  \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n = 
                  \<Sigma>\<^sub>e M (\<lambda>k. t k \<cdot>\<^sub>s (g k)) (card (f ` {j. j \<le> n}) - Suc 0)"  
apply (simp add:same_togetherTr[of A H])
done

lemma (in Module) one_last:"\<lbrakk>ideal R A; H \<subseteq> carrier M; 
      s \<in> {j. j \<le> (Suc n)} \<rightarrow> A; f \<in> {j. j \<le> (Suc n)} \<rightarrow> H; 
      bij_to f {j. j \<le> (Suc n)} H; j \<le> (Suc n); j \<noteq> (Suc n)\<rbrakk> \<Longrightarrow> 
 \<exists>t \<in> {j. j \<le> (Suc n)} \<rightarrow> A. \<exists>g \<in> {j. j \<le> (Suc n)} \<rightarrow> H.  
  \<Sigma>\<^sub>e M (\<lambda>k. s k  \<cdot>\<^sub>s (f k)) (Suc n) =  \<Sigma>\<^sub>e M (\<lambda>k. t k  \<cdot>\<^sub>s (g k)) (Suc n) \<and>
  g (Suc n) = f j \<and> t (Suc n) = s j \<and> bij_to g {j. j \<le> (Suc n)} H"  
apply (cut_tac sc_Ring)
apply (subgoal_tac "(\<lambda>k. s k \<cdot>\<^sub>s (f k)) \<in> {j. j \<le> Suc n} \<rightarrow> carrier M")
apply (frule transpos_hom[of j "Suc n" "Suc n"], simp, assumption,
       frule transpos_inj[of j "Suc n" "Suc n"], simp, assumption,
       frule_tac f1 = "\<lambda>k.  s k \<cdot>\<^sub>s (f k)" and n1 = n and h1 = 
         "transpos j (Suc n)" in addition2 [THEN sym], assumption+,
       simp del:nsum_suc)
prefer 2  
    apply (rule Pi_I, rule sc_mem,
           simp add:Pi_def Ring.ideal_subset,
           simp add:Pi_def subsetD)
 apply (frule cmp_fun[of "transpos j (Suc n)" "{j. j \<le> Suc n}" 
                         "{j. j \<le> Suc n}" s A], assumption+,
        frule cmp_fun[of "transpos j (Suc n)" "{j. j \<le> Suc n}" 
                         "{j. j \<le> Suc n}" f H], assumption+)
 apply (simp del:nsum_suc add:l_comb_transpos[of A H])
 apply (subgoal_tac "bij_to (cmp f (transpos j (Suc n))) {j. j \<le> (Suc n)} H") 
 apply (subgoal_tac "(cmp f (transpos j (Suc n))) (Suc n) = f j")
 apply (subgoal_tac "(cmp s (transpos j (Suc n))) (Suc n) = s j")
 apply blast
 apply (simp add:cmp_def, simp add:transpos_ij_2,
        simp add:cmp_def, simp add:transpos_ij_2)
 apply (simp add:bij_to_def, rule conjI,
        rule cmp_surj[of "transpos j (Suc n)" "{j. j \<le> Suc n}" 
          "{j. j \<le> Suc n}" f H], assumption+,
        simp add:transpos_surjec, assumption+, simp)
 apply (rule cmp_inj[of "transpos j (Suc n)" "{j. j \<le> Suc n}" 
          "{j. j \<le> Suc n}" f H], assumption+, simp)
done
 
lemma (in Module) finite_lin_spanTr1:"\<lbrakk>ideal R A; z \<in> carrier M\<rbrakk> \<Longrightarrow>
      h \<in> {j. j \<le> (n::nat)} \<rightarrow> {z} \<and> t \<in> {j. j \<le> n} \<rightarrow> A  \<longrightarrow> 
      (\<exists>s\<in>{0::nat} \<rightarrow> A. \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s (h j)) n =  s 0 \<cdot>\<^sub>s z)"
apply (induct_tac n)
 apply (rule impI)
 apply ((erule conjE)+, simp)
 apply blast 

apply (rule impI) apply (erule conjE)+
 apply (frule func_pre [of _ _ "{z}"], frule func_pre [of _ _ "A"])
apply (simp del:nsum_suc, erule bexE, simp,
       frule_tac f = h and A = "{j. j \<le> Suc n}" and B = "{z}" and x = "Suc n"
       in funcset_mem, simp, simp,
       frule_tac f = t and A = "{j. j \<le> Suc n}" and B = A and x = "Suc n" in
        funcset_mem, simp, cut_tac sc_Ring,
       frule_tac h = "s 0" in Ring.ideal_subset[of R A], assumption+,
       frule_tac h = "t (Suc n)" in Ring.ideal_subset[of R A], assumption+)
 apply (simp add:sc_l_distr[THEN sym])
 apply (subgoal_tac "(\<lambda>l\<in>{0::nat}. (s 0 \<plusminus>\<^bsub>R\<^esub> (t (Suc n)))) \<in> {0} \<rightarrow> A")
apply (subgoal_tac "(s 0 \<plusminus>\<^bsub>R\<^esub> t (Suc n)) \<cdot>\<^sub>s z = (\<lambda>l\<in>{0::nat}. (s 0 \<plusminus>\<^bsub>R\<^esub> (t (Suc n)))) 0 \<cdot>\<^sub>s z ") apply blast
 apply simp 
 apply (rule Pi_I) apply simp
 apply (rule Ring.ideal_pOp_closed, assumption+)
done

lemma (in Module) single_span:"\<lbrakk>ideal R A; z \<in> carrier M;
    h \<in> {j. j \<le> (n::nat)} \<rightarrow> {z}; t \<in> {j. j \<le> n} \<rightarrow> A\<rbrakk> \<Longrightarrow> 
     \<exists>s\<in>{0::nat} \<rightarrow> A. \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s (h j)) n =  s 0 \<cdot>\<^sub>s z"
apply (simp add:finite_lin_spanTr1)
done
(*
lemma (in Module) finite_lin_spanTr2:"\<lbrakk>ideal R A; \<forall>m. 
(\<exists>n1. \<exists>f\<in>{j. j \<le> n1} \<rightarrow> h ` {j. j \<le> n}. \<exists>s\<in>{j. j \<le> n1} \<rightarrow> A. 
  m = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n1) \<longrightarrow> 
     (\<exists>s\<in>{j. j \<le> n} \<rightarrow> A. m = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (h j)) n); 
  h \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier M; f \<in> {j. j \<le> n1} \<rightarrow> h ` {j. j \<le> n}; 
  s \<in> {j. j \<le> n1} \<rightarrow> A; m = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n1\<rbrakk> \<Longrightarrow> 
  \<exists>sa\<in>{j. j \<le> (Suc n)} \<rightarrow> A. \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) n1 = 
    \<Sigma>\<^sub>e M (\<lambda>j. sa j \<cdot>\<^sub>s (h j)) n \<plusminus> (sa (Suc n) \<cdot>\<^sub>s (h (Suc n)))"
 apply (frule_tac 
 apply (subgoal_tac "\<exists>l\<in>{j. j \<le> n} \<rightarrow> A. m = \<Sigma>\<^sub>e M (\<lambda>j. l j \<cdot>\<^sub>s (h j)) n")
 prefer 2 
 apply (thin_tac "h \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier M")
 apply blast
 apply (thin_tac " \<forall>m. (\<exists>n1. \<exists>f\<in>Nset n1 \<rightarrow> h ` Nset n.
  \<exists>s\<in>Nset n1 \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n1) \<longrightarrow>
              (\<exists>s\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j.  s j \<star>\<^sub>M (h j)) n)")
 apply (subgoal_tac "\<forall>l\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n \<longrightarrow> (\<exists>sa\<in>Nset (Suc n) \<rightarrow> A. e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n1 = e\<Sigma> M (\<lambda>j. sa j \<star>\<^sub>M (h j)) n +\<^sub>M  (sa (Suc n) \<star>\<^sub>M (h (Suc n))))")
 apply blast
 apply (thin_tac "\<exists>l\<in>Nset n \<rightarrow> A. m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (rule ballI) apply (rule impI)
 apply (frule sym) apply (thin_tac "m = e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n1")
 apply simp
 apply (thin_tac "m = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (thin_tac "e\<Sigma> M (\<lambda>j. s j \<star>\<^sub>M (f j)) n1 = e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n")
 apply (subgoal_tac "jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R)) \<in> Nset (Suc n) \<rightarrow> A")
 apply (subgoal_tac " e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n =
  e\<Sigma> M (\<lambda>j. (jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R))) j \<star>\<^sub>M (h j)) n +\<^sub>M  ((jointfun n l 0 (\<lambda>x\<in>Nset 0. (0\<^sub>R))) (Suc n)) \<star>\<^sub>M (h (Suc n))")
 apply blast
 apply (subgoal_tac "jointfun n l 0 (\<lambda>x\<in>Nset 0. 0\<^sub>R) (Suc n) \<star>\<^sub>M (h (Suc n)) =
  0\<^sub>M") apply simp
 apply (subgoal_tac "e\<Sigma> M (\<lambda>j. jointfun n l 0 (\<lambda>x\<in>Nset 0. 0\<^sub>R) j \<star>\<^sub>M (h j)) n =
 e\<Sigma> M (\<lambda>j. l j \<star>\<^sub>M (h j)) n ") apply simp
 apply (frule module_is_ag [of "R" "M"], assumption+)
 apply (subst ag_r_zero, assumption+)
 apply (subgoal_tac "(\<lambda>j. l j \<star>\<^sub>M (h j)) \<in> Nset n \<rightarrow> carrier M")
 apply (rule eSum_mem, assumption+) apply (simp add:n_in_Nsetn)
 apply (rule univar_func_test) apply (rule ballI) 
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"])
 apply (simp add:funcset_mem) apply simp
 apply (rule eSum_eq)
 apply (rule module_is_ag [of "R" "M"], assumption+)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (frule_tac x = x and n = n in Nset_le)
 apply (insert Nset_nonempty[of "0"]) 
 apply (simp add:jointfun_def)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"]) 
 apply (simp add:funcset_mem)
 apply (rule univar_func_test) apply (rule ballI)
 apply (rule sprod_mem, assumption+)
 apply (simp add:funcset_mem ideal_subset)
 apply (frule func_pre [of "h" _ "carrier M"])
 apply (simp add:funcset_mem)
apply (rule ballI)
 apply (frule_tac x = la and n = n in Nset_le)
 apply (simp add:jointfun_def)
 apply (subgoal_tac "0 \<in> Nset 0")
 apply (simp add:jointfun_def sliden_def slide_def)
 apply (rule sprod_0_m, assumption+) 
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:funcset_mem) apply (simp add:n_in_Nsetn)+ 
apply (frule_tac f = l and n = n and A = A and g = "\<lambda>x\<in>Nset 0. 0\<^sub>R" and m = 0
      and B = A in jointfun_hom0)
 apply (rule univar_func_test) apply (rule ballI) apply (simp add:Nset_def)
 apply (simp add:ideal_zero) apply simp
done *) 

definition
  coeff_at_k :: "[('r, 'm) Ring_scheme, 'r, nat] \<Rightarrow> (nat \<Rightarrow> 'r)" where
  "coeff_at_k R a k = (\<lambda>j. if j = k then a else (\<zero>\<^bsub>R\<^esub>))" 

lemma card_Nset_im:"f \<in> {j. j \<le> (n::nat)} \<rightarrow> A \<Longrightarrow> 
                      (Suc 0) \<le> card (f `{j. j \<le> n})"
apply (cut_tac image_Nsetn_card_pos[of f n])
apply (frule_tac m = 0 and n = "card (f ` {i. i \<le> n})" in Suc_leI,
        assumption+)
done 

lemma (in Module) eSum_changeTr1:"\<lbrakk>ideal R A; 
  t \<in> {k. k \<le> (card (f ` {j. j \<le> (n1::nat)}) - Suc 0)} \<rightarrow> A; 
  g \<in> {k. k \<le> (card (f ` {j. j \<le> n1}) - Suc 0)} \<rightarrow> f `{j. j \<le> n1}; 
  Suc 0 < card (f `{j. j \<le> n1}); g x = h (Suc n); x = Suc n; 
card (f `{j. j \<le> n1}) - Suc 0 =  Suc (card (f ` {j. j \<le> n1}) - Suc 0 - Suc 0)\<rbrakk>
  \<Longrightarrow> 
 \<Sigma>\<^sub>e M (\<lambda>k. t k  \<cdot>\<^sub>s (g k)) (card (f ` {j. j \<le> n1}) - Suc 0) =  
 \<Sigma>\<^sub>e M (\<lambda>k. t k  \<cdot>\<^sub>s (g k)) (card (f ` {j. j \<le> n1}) - Suc 0 - Suc 0) \<plusminus>  
    (t (Suc (card (f ` {j. j \<le> n1}) - Suc 0 - Suc 0))  \<cdot>\<^sub>s 
                (g ( Suc (card (f ` {j. j \<le> n1}) - Suc 0 - Suc 0))))"  
apply simp
done

definition
  zeroi :: "[('r, 'm) Ring_scheme] \<Rightarrow> nat \<Rightarrow> 'r" where
  "zeroi R = (\<lambda>j. \<zero>\<^bsub>R\<^esub>)" 

lemma zeroi_func:"\<lbrakk>Ring R; ideal R A\<rbrakk> \<Longrightarrow>  zeroi R \<in> {j. j \<le> 0} \<rightarrow> A"
by (simp add:zeroi_def Ring.ideal_zero)

lemma (in Module) prep_arrTr1:"\<lbrakk>ideal R A; h \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier M;
 f \<in> {j. j \<le> (n1::nat)} \<rightarrow> h ` {j. j \<le> (Suc n)}; s \<in> {j. j \<le> n1}\<rightarrow> A; 
 m = l_comb R M n1 s f\<rbrakk> \<Longrightarrow> 
 \<exists>l\<in>{j. j \<le> (Suc n)}. (\<exists>s\<in>{j. j \<le> (l::nat)} \<rightarrow> A. 
 \<exists>g\<in> {j. j \<le> l} \<rightarrow> h `{j. j \<le> (Suc n)}. m = l_comb R M l s g \<and> 
                      bij_to g {j. j \<le> l} (f ` {j. j \<le> n1}))"
apply (cut_tac sc_Ring)
apply (frule_tac s = s and n = n1 and f = f in  same_together[of A 
      "h ` {j. j \<le> (Suc n)}"]) 
 apply (simp add:image_sub0, assumption+)
 apply (erule bexE)+ 
 apply (simp add:l_comb_def, erule conjE)
 apply (thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) n1 =
           \<Sigma>\<^sub>e M (\<lambda>k. t k \<cdot>\<^sub>s g k) (card (f ` {j. j \<le> n1}) - Suc 0)")
 apply (subgoal_tac "(card (f ` {j. j \<le> n1}) - Suc 0) \<in> {j. j \<le> Suc n}")
 apply (subgoal_tac "g \<in> {k. k \<le> (card (f `{j. j \<le> n1}) - Suc 0)} \<rightarrow>
                         h ` {j. j \<le> Suc n}")
 apply (subgoal_tac "bij_to g {k. k \<le> (card (f ` {j. j \<le> n1}) - Suc 0)} (f ` {j. j \<le> n1})")
 apply blast
 prefer 2 
  apply (frule_tac f = f and A = "{j. j \<le> n1}" and B = "h ` {j. j \<le> Suc n}" 
          in image_sub0, simp)
  apply (rule extend_fun, assumption+)
 apply (simp add:bij_to_def)
apply (rule_tac A = "f ` {j. j \<le> n1}" and n = "card (f `{j. j \<le> n1}) - Suc 0" and f = g in Nset2finite_inj)
 apply (rule finite_imageI, simp)
 apply (frule_tac f = f and n = n1 and A = "h ` {j. j \<le> (Suc n)}" in card_Nset_im)
 apply (simp, assumption)
apply (subgoal_tac "finite (h ` {j. j \<le> (Suc n)})")
apply (frule_tac f = f and A = "{j. j \<le> n1}" and B = "h ` {j. j \<le> (Suc n)}" 
       in image_sub0, simp)
 apply (cut_tac B = "h ` {j. j \<le> (Suc n)}" and A = "f ` {j. j \<le> n1}" in 
        card_mono, simp,  assumption+,
        insert finite_Collect_le_nat [of "Suc n"],
        frule card_image_le [of "{j. j \<le> (Suc n)}" "h"],
        frule_tac i = "card (f ` {j. j \<le> n1})" and 
         j = "card (h ` {j. j \<le> (Suc n)})" and k = "card {j. j \<le> (Suc n)}" in
        le_trans, assumption+)
 apply simp
 apply (rule finite_imageI, simp)
done

lemma two_func_imageTr:"\<lbrakk> h \<in> {j. j \<le> Suc n} \<rightarrow> B; 
   f \<in> {j. j \<le> (m::nat)} \<rightarrow> h ` {j. j \<le> Suc n};  h (Suc n) \<notin> f ` {j. j \<le> m}\<rbrakk>
       \<Longrightarrow> f \<in> {j. j \<le> m} \<rightarrow> h ` {j. j \<le> n}" 
apply (rule Pi_I)
    apply (frule_tac x = x and f = f and A = "{j. j \<le> m}" and 
           B = "h ` {j. j \<le> Suc n}" in funcset_mem, assumption)
   apply (thin_tac "h \<in> {j. j \<le> Suc n} \<rightarrow> B")
   apply (rule contrapos_pp, simp+)
     apply (simp add:image_def[of h])
     apply (erule exE, erule conjE)
     apply (case_tac "xa \<noteq> Suc n",
            frule_tac m = xa and n = "Suc n" in noteq_le_less, assumption)
          apply (
            thin_tac "xa \<le> Suc n",
            frule_tac x = xa and n = "Suc n" in less_le_diff,
            thin_tac "xa < Suc n", simp) apply blast
     apply simp
     apply (subgoal_tac "(f x) \<in> f ` {j. j \<le> m}", simp)
       apply (thin_tac "h (Suc n) \<notin> f ` {j. j \<le> m}",
                 thin_tac "\<forall>x\<le>n. h (Suc n) \<noteq> h x",
                 thin_tac "f x = h (Suc n)",
                 thin_tac "xa = Suc n")
     apply (simp add:image_def, blast)
done

lemma (in Module) finite_lin_spanTr3_0:"\<lbrakk>bij_to g {j. j \<le> l} (g `{j. j \<le> l});
      ideal R A; 
     \<forall>na. \<forall>s\<in>{j. j \<le> na} \<rightarrow> A.
                \<forall>f\<in>{j. j \<le> na} \<rightarrow> h ` {j. j \<le> n}.
                   \<exists>t\<in>{j. j \<le> n} \<rightarrow> A. l_comb R M na s f = l_comb R M n t h;
     h \<in> {j. j \<le> Suc n} \<rightarrow> carrier M; s \<in> {j. j \<le> m} \<rightarrow> A;
     f \<in> {j. j \<le> m} \<rightarrow> h ` {j. j \<le> Suc n}; 
     l \<le> Suc n; sa \<in> {j. j \<le> l} \<rightarrow> A; g \<in> {j. j \<le> l} \<rightarrow> h ` {j. j \<le> Suc n};
     0 < l; f ` {j. j \<le> m} = g ` {j. j \<le> l}; h (Suc n) = g l\<rbrakk>
 \<Longrightarrow> \<exists>t\<in>{j. j \<le> Suc n} \<rightarrow> A. l_comb R M l sa g = l_comb R M (Suc n) t h"
  apply (cut_tac sc_Ring)
  apply (subgoal_tac "l_comb R M l sa g = l_comb R M (Suc (l - Suc 0)) sa g",
         simp del:Suc_pred,
         thin_tac "l_comb R M l sa g = l_comb R M (Suc (l - Suc 0)) sa g",
         simp del:Suc_pred add:l_comb_def)
  apply (drule_tac x = "l - Suc 0" in spec,
         drule_tac x = sa in bspec)
        
  apply (rule Pi_I, simp)
        apply (rule_tac x = x and f = sa and A = "{j. j \<le> l}"and B = A
               in funcset_mem, assumption, simp) (*
        apply (rule_tac i = x and j = "l - Suc 0" and k = l in le_trans)
apply (
               assumption, subst Suc_le_mono[THEN sym], simp) *)
  apply (drule_tac x = g in bspec,
         thin_tac "f \<in> {j. j \<le> m} \<rightarrow> h ` {j. j \<le> Suc n}",
         thin_tac "sa \<in> {j. j \<le> l} \<rightarrow> A",
         thin_tac "f ` {j. j \<le> m} = g ` {j. j \<le> l}")
      apply (rule Pi_I, simp)
      apply (frule_tac x = x and f = g and A = "{j. j \<le> l}" and 
         B = "h ` {j. j \<le> Suc n}" in funcset_mem)
      apply simp (*
      apply (rule_tac i = x and j = "l - Suc 0" and k = l in Nat.le_trans,
             assumption, subst Suc_le_mono[THEN sym], simp) *)
      apply (unfold bij_to_def, frule conjunct2, fold bij_to_def,
             thin_tac "bij_to g {j. j \<le> l} (g ` {j. j \<le> l})",
             thin_tac "g \<in> {j. j \<le> l} \<rightarrow> h ` {j. j \<le> Suc n}")
      apply (simp add:image_def, erule exE, erule conjE)
      apply (case_tac "xa = Suc n", simp add:inj_on_def,
             drule_tac a = x in forall_spec) apply simp
(*
      apply (frule_tac i = x and j = "l - Suc 0" and k = l in Nat.le_trans,
              subst Suc_le_mono[THEN sym], simp, assumption) *)
      apply(drule_tac a = l in forall_spec, simp) 
      apply (cut_tac n1 = l and m1 = "l - Suc 0" in Suc_le_mono[THEN sym])
             apply simp
     apply (frule_tac m = xa and n = "Suc n" in noteq_le_less, assumption,
            thin_tac "xa \<le> Suc n",
            frule_tac x = xa and n = "Suc n" in less_le_diff,
            thin_tac "xa < Suc n", simp)
      apply blast
      apply (erule bexE, simp)
      apply (rotate_tac -4, frule sym, thin_tac "h (Suc n) = g l", simp)
   apply (frule_tac f = t and n = n and A = A and g = "\<lambda>k\<in>{0::nat}. sa l"
          and m = 0 and B = A in jointfun_hom0,
          simp add:Pi_def, simp)
   apply (subgoal_tac " \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s h j) n \<plusminus> sa l \<cdot>\<^sub>s h (Suc n) =
           \<Sigma>\<^sub>e M (\<lambda>j. (jointfun n t 0 (\<lambda>k\<in>{0}. sa l)) j \<cdot>\<^sub>s h j) (Suc n)",
          simp, blast) 
   apply (cut_tac H = "carrier M" and A = A and s = t and f = h and n = n and
          m = 0 and t = "\<lambda>k\<in>{0}. sa l" in l_comb_jointfun_jf)
          apply simp+ 
          apply (simp add:Pi_def)
          apply simp
   apply (simp add:jointfun_def sliden_def, simp)
done
 
lemma (in Module) finite_lin_spanTr3:"ideal R A \<Longrightarrow> 
       h \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier M \<longrightarrow> 
      (\<forall>na. \<forall>s \<in> {j. j \<le> (na::nat)} \<rightarrow> A. 
       \<forall>f\<in> {j. j \<le> na} \<rightarrow> (h ` {j. j \<le> n}). (\<exists>t \<in> {j. j \<le> n} \<rightarrow> A. 
       l_comb R M na s f = l_comb R M n t h))"
apply (cut_tac sc_Ring)
apply (induct_tac n)
 apply (rule impI, rule allI, (rule ballI)+) 
 apply (insert Nset_nonempty [of "0"]) 
 apply (simp add:l_comb_def)
 apply (frule_tac z = "h 0" and h = f and t = s and n = na in 
          single_span [of A])
 apply (simp add:Pi_def)
 apply assumption+
(********** n = 0 done ***********)
apply (rule impI, rule allI, (rule ballI)+) 
 apply (frule func_pre, simp)
 apply (case_tac "h (Suc n) \<notin>  f ` {j. j \<le> na}")
  apply (frule_tac h = h and n = n and B = "carrier M" and f = f and
         m = na in two_func_imageTr, assumption+)
  apply (drule_tac x = na in spec,
         drule_tac x = s in bspec, assumption,
         drule_tac x = f in bspec, assumption)
        
  apply (erule bexE, simp )
  apply (thin_tac "l_comb R M na s f = l_comb R M n t h") 
apply (simp add:l_comb_def)
 apply (subgoal_tac "\<Sigma>\<^sub>e M (\<lambda>j. t j  \<cdot>\<^sub>s (h j)) n =
        \<Sigma>\<^sub>e M (\<lambda>j. (jointfun n t 0 (zeroi R)) j \<cdot>\<^sub>s (h j)) (Suc n)", simp,
        thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s h j) n =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun n t 0 (zeroi R) j \<cdot>\<^sub>s h j) n \<plusminus>
        jointfun n t 0 (zeroi R) (Suc n) \<cdot>\<^sub>s h (Suc n)")
 apply (frule_tac f = t and n = n and g = "zeroi R" and m = 0 and A = A and 
        B = A in jointfun_hom)
        apply (rule zeroi_func, assumption+, simp, blast)
 apply (cut_tac H = "carrier M" and s = t and n = n and f = h and m = 0 and 
        t = "zeroi R" in l_comb_jointfun_jf[of _ A],
        simp, assumption+, simp,
        rule zeroi_func, assumption+)
 apply (simp,
       thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. jointfun n t 0 (zeroi R) j \<cdot>\<^sub>s h j) n =
        \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s h j) n",
        simp add:jointfun_def sliden_def zeroi_def,
        subst sc_0_m, simp add:Pi_def,
        subst ag_r_zero,
        rule nsum_mem, rule allI, rule impI, rule sc_mem,
               simp add:Pi_def Ring.ideal_subset,
               simp add:Pi_def,
         simp)

(*** case h (Suc n) \<notin>  f ` (Nset na) done ***)

apply simp
apply (frule_tac h = h and n = n and m = "l_comb R M na s f" in 
               prep_arrTr1 [of "A"], assumption+, simp)
apply (erule bexE)+
 apply (simp, (erule conjE)+)
 apply (case_tac "l = 0", simp)
 apply (unfold bij_to_def, frule conjunct1, frule conjunct2, fold bij_to_def)
 apply (thin_tac "l_comb R M na s f = l_comb R M 0 sa g")
 apply (simp add:l_comb_def)
 apply (simp add:surj_to_def, rotate_tac -1, frule sym, 
        thin_tac "{g 0} = f ` {j. j \<le> na}", simp,
        rotate_tac -6, frule sym, thin_tac "h (Suc n) = g 0", simp)
 apply (cut_tac f = "zeroi R" and n = n and g = "\<lambda>j. sa 0" and m = 0 and 
         A = A and B = A in jointfun_hom0)
        apply (simp add:zeroi_def Ring.ideal_zero)
        apply (simp add:Pi_def)
        apply simp
 apply (subgoal_tac "sa 0 \<cdot>\<^sub>s h (Suc n) = nsum M (\<lambda>j. (jointfun n (zeroi R) 0 
         (\<lambda>j. sa 0) j \<cdot>\<^sub>s h j)) (Suc n)", simp,
        thin_tac "sa 0 \<cdot>\<^sub>s h (Suc n) =
        \<Sigma>\<^sub>e M (\<lambda>j. jointfun n (zeroi R) 0 (\<lambda>j. sa 0) j \<cdot>\<^sub>s h j) n \<plusminus>
        jointfun n (zeroi R) 0 (\<lambda>j. sa 0) (Suc n) \<cdot>\<^sub>s h (Suc n)",
        blast)
 apply simp
 apply (cut_tac n = n and f = "\<lambda>j. jointfun n (zeroi R) 0 (\<lambda>j. sa 0) j \<cdot>\<^sub>s h j"
        in nsum_zeroA)
 apply (rule allI, rule impI,
        simp add:jointfun_def zeroi_def,
        rule sc_0_m, simp add:Pi_def, simp,
       thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. jointfun n (zeroi R) 0 (\<lambda>j. sa 0) j \<cdot>\<^sub>s h j) n = \<zero>")
 apply (simp add:jointfun_def sliden_def,
        subst ag_l_zero,
        rule sc_mem, simp add:Pi_def Ring.ideal_subset,
        simp add:Pi_def, simp)
 (**** l = 0 done ***)
apply (simp)
 apply (thin_tac "l_comb R M na s f = l_comb R M l sa g")
 apply (unfold bij_to_def, frule conjunct1, frule conjunct2, fold bij_to_def)
 apply (simp add:surj_to_def, rotate_tac -2, frule sym,
        thin_tac "g ` {j. j \<le> l} = f ` {j. j \<le> na}", simp)
  apply (subgoal_tac "\<exists>x\<in>{j. j \<le> l}. h (Suc n) = g x")  
  prefer 2  apply (simp add:image_def) 
apply (erule bexE)
  apply (case_tac "x = l", simp)
apply (frule_tac g = g and l = l and A = A and h = h and n = n and s = s and
       m = na and f = f and l = l and sa = sa in finite_lin_spanTr3_0,
       assumption+)

apply (subgoal_tac "l_comb R M l sa g = l_comb R M (Suc (l - Suc 0)) sa g")
   prefer 2 apply simp
  apply (simp del:nsum_suc Suc_pred,
          thin_tac "l_comb R M l sa g = l_comb R M (Suc (l - Suc 0)) sa g",
          simp del:nsum_suc Suc_pred add:l_comb_def)
   apply (cut_tac f1 = "\<lambda>j. sa j \<cdot>\<^sub>s g j" and n1 = "l - Suc 0" and
          h1 = "transpos x (Suc (l - Suc 0))" in addition2[THEN sym],
          thin_tac "\<forall>na. \<forall>s\<in>{j. j \<le> na} \<rightarrow> A.
                \<forall>f\<in>{j. j \<le> na} \<rightarrow> h ` {j. j \<le> n}.
                   \<exists>t\<in>{j. j \<le> n} \<rightarrow> A.
                      \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) na = \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s h j) n",
              rule Pi_I, simp)
       apply (rule sc_mem, 
              simp add:Pi_def Ring.ideal_subset,
              frule_tac f = h and A = "{j. j \<le> Suc n}" and B = "carrier M" in
              image_sub0,
              frule_tac x = xa and f = g and A = "{j. j \<le> l}" and 
              B = "h ` {j. j \<le> Suc n}" in funcset_mem, simp, simp add:subsetD)
       apply (simp,
             rule_tac i = x and n = l and j = l in transpos_hom,
             assumption+, simp, assumption+)
       apply (simp,
              rule_tac i = x and n = l and j = l in transpos_inj,
              assumption+, simp, assumption+)
    apply (simp del:Suc_pred nsum_suc)
    apply (subst l_comb_transpos[of A "carrier M"], assumption, simp,
           simp, simp,
           rule Pi_I,
           frule_tac f = h and A = "{j. j \<le> Suc n}" and B = "carrier M" in
              image_sub0,
              frule_tac x = xa and f = g and A = "{j. j \<le> l}" and 
              B = "h ` {j. j \<le> Suc n}" in funcset_mem, simp, simp add:subsetD,
            simp)  
     apply (simp del:Suc_pred, simp,
            thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. sa j \<cdot>\<^sub>s g j) (l - Suc 0) \<plusminus> sa l \<cdot>\<^sub>s g l =
        \<Sigma>\<^sub>e M (cmp (\<lambda>j. sa j \<cdot>\<^sub>s g j) (transpos x l)) (l - Suc 0) \<plusminus>
        cmp (\<lambda>j. sa j \<cdot>\<^sub>s g j) (transpos x l) l")

apply (cut_tac g = "cmp g (transpos x l)" and l = l and A = A and
      h = h and n = n and s = s and m = na and f = f and l = l and
      sa = "cmp sa (transpos x l)" in finite_lin_spanTr3_0)

   apply (frule_tac i = x and n = l and j = l in transpos_hom,
          simp, assumption)
   apply (cut_tac n = l in Nat.le_refl)
   apply (frule_tac i = x and n = l and j = l in transpos_surjec, assumption+)
   apply (frule_tac f = "transpos x l" and A = "{j. j \<le> l}" and 
         B = "{j. j \<le> l}" and g = g and C = "g ` {j. j \<le> l}" in cmp_surj,
         assumption+)
   apply (rule_tac f = g and A = "{j. j \<le> l}" and B = "h ` {j. j \<le> Suc n}"
          in func_to_img, assumption)
   apply (simp add:bij_to_def)
   apply (subst bij_to_def, simp)
   apply (subgoal_tac "cmp g (transpos x l) ` {j. j \<le> l} = g ` {j. j \<le> l}",
          simp) 
   apply (frule_tac f = "transpos x l" and A = "{j. j \<le> l}" and 
         B = "{j. j \<le> l}" and g = g and C = "h ` {j. j \<le> Suc n}" in cmp_inj,
         assumption+)
   apply (rule_tac i = x and n = l and j = l in transpos_inj, assumption,
          simp, assumption, simp add:bij_to_def,
          assumption)
   apply (simp add:cmp_fun_image, simp add:surj_to_def)

   apply assumption+ 
   apply (simp add:l_comb_def)
   apply assumption+
   
   apply (rule Pi_I)
   apply (simp add:cmp_def)
   apply (cut_tac n = l in Nat.le_refl,
          frule_tac i = x and n = l and j = l and l = xa in transpos_mem,
          assumption+,
          simp add:Pi_def)
   apply (rule Pi_I,
          simp add:cmp_def,
          cut_tac n = l in Nat.le_refl,
          frule_tac i = x and n = l and j = l and l = xa in transpos_mem,
          assumption+,
          simp add:Pi_def)
   apply simp
   
   apply (cut_tac n = l in Nat.le_refl,
          frule_tac i = x and n = l and j = l in transpos_surjec, assumption+)
     apply (frule_tac i = x and n = l and j = l in transpos_hom,
           simp, assumption)
   apply (frule_tac f = "transpos x l" and A = "{i. i \<le> l}" and 
          B = "{i. i \<le> l}" and g = g and C = "h ` {j. j \<le> Suc n}" in
          cmp_fun_image, assumption+)
   apply (simp add:surj_to_def)
   apply (simp add:cmp_def)
   apply (simp add:transpos_ij_2)
   apply (erule bexE)
   apply (thin_tac "\<forall>na. \<forall>s\<in>{j. j \<le> na} \<rightarrow> A.
                \<forall>f\<in>{j. j \<le> na} \<rightarrow> h ` {j. j \<le> n}.
                   \<exists>t\<in>{j. j \<le> n} \<rightarrow> A.
                      \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s f j) na = \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s h j) n")
   apply (rename_tac n na s f l sa g x sb)
  apply (subgoal_tac "l_comb R M l (cmp sa (transpos x l)) 
   (cmp g (transpos x l)) = l_comb R M (Suc (l - Suc 0)) 
    (cmp sa (transpos x l)) (cmp g (transpos x l)) ",
     simp del:Suc_pred,
     thin_tac "l_comb R M l (cmp sa (transpos x l)) (cmp g (transpos x l)) =
        l_comb R M (Suc n) sb h")
  apply (simp del:Suc_pred add:l_comb_def, simp,
         thin_tac " \<Sigma>\<^sub>e M (\<lambda>j. cmp sa (transpos x l) j \<cdot>\<^sub>s
                  cmp g (transpos x l) j) (l - Suc 0) \<plusminus>
         cmp sa (transpos x l) l \<cdot>\<^sub>s cmp g (transpos x l) l =
         \<Sigma>\<^sub>e M (\<lambda>j. sb j \<cdot>\<^sub>s h j) n \<plusminus> sb (Suc n) \<cdot>\<^sub>s g x")
   apply (rotate_tac -3, frule sym, thin_tac "h (Suc n) = g x", simp)
   apply blast

   apply simp
done
     
lemma (in Module) finite_lin_span:
"\<lbrakk>ideal R A;  h \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier M; s \<in> {j. j \<le> (n1::nat)} \<rightarrow> A;
 f \<in> {j. j \<le> n1} \<rightarrow> h ` {j. j \<le> n}\<rbrakk> \<Longrightarrow> \<exists>t\<in>{j. j \<le> n} \<rightarrow> A.
              l_comb R M n1 s f = l_comb R M n t h"
apply (simp add:finite_lin_spanTr3)
done

subsection "Free generators"

definition
  free_generator :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 'a set]
        \<Rightarrow> bool" where
 "free_generator R M H \<longleftrightarrow> generator R M H \<and>
      (\<forall>n. (\<forall>s f. (s \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R \<and>
                   f \<in> {j. j \<le> n} \<rightarrow> H \<and> inj_on f {j. j \<le> n} \<and> 
         l_comb R M n s f = \<zero>\<^bsub>M\<^esub>) \<longrightarrow> s \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}))"

lemma (in Module) free_generator_generator:"free_generator R M H \<Longrightarrow>
                  generator R M H"
by (simp add:free_generator_def)

lemma (in Module) free_generator_sub:"free_generator R M H \<Longrightarrow> 
                    H \<subseteq> carrier M"
by (simp add:free_generator_def generator_def)

lemma (in Module) free_generator_nonzero:"\<lbrakk>\<not> (zeroring R); 
                free_generator R M H; h \<in> H\<rbrakk> \<Longrightarrow> h \<noteq> \<zero>"
apply (cut_tac sc_Ring)
apply (rule contrapos_pp, simp+)
 apply (simp add:free_generator_def, (erule conjE)+)
 apply (subgoal_tac "(\<lambda>t. 1\<^sub>r\<^bsub>R\<^esub>) \<in> {j. j \<le> (0::nat)} \<rightarrow> carrier R")
 apply (subgoal_tac "(\<lambda>t. \<zero>) \<in> {j. j \<le> (0::nat)} \<rightarrow> H \<and> 
                     inj_on (\<lambda>t. \<zero>) {j. j \<le> (0::nat)} \<and>
        l_comb R M 0 (\<lambda>t.  1\<^sub>r\<^bsub>R\<^esub>) (\<lambda>t.  \<zero>) =  \<zero>")
 apply (subgoal_tac "(\<lambda>t.  1\<^sub>r\<^bsub>R\<^esub>) \<in> {j. j \<le> (0::nat)} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}") 
 prefer 2 apply blast
 apply (frule_tac f = "\<lambda>t. 1\<^sub>r\<^bsub>R\<^esub>" and A = "{j. j \<le> (0::nat)}" and B = "{\<zero>\<^bsub>R\<^esub>}" 
        and x = 0 in funcset_mem, simp, simp)
 apply (frule Ring.Zero_ring1 [of "R"], assumption+, simp)
apply simp
 apply (thin_tac "\<forall>n s. s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and>
           (\<exists>f. f \<in> {j. j \<le> n} \<rightarrow> H \<and>
                inj_on f {j. j \<le> n} \<and> l_comb R M n s f = \<zero>) \<longrightarrow>
           s \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}")
 apply (simp add:l_comb_def)
 apply (rule sc_a_0)
 apply (simp add:Ring.ring_one)
 apply (simp add:Ring.ring_one)
done

lemma (in Module) has_free_generator_nonzeroring:" \<lbrakk>free_generator R M H; 
      \<exists>p \<in> linear_span R M (carrier R) H. p \<noteq> \<zero> \<rbrakk>  \<Longrightarrow> \<not> zeroring R"
apply (erule bexE, simp add:linear_span_def)
 apply (case_tac "H = {}", simp, simp)
 apply (erule exE, (erule bexE)+, simp,
        thin_tac "p = l_comb R M n s f")
apply (rule contrapos_pp, simp+)
 apply (simp add:zeroring_def, erule conjE)
 apply (frule Ring.ring_one[of "R"], simp)
 apply (simp add:l_comb_def)
 apply (cut_tac n = n and f = "\<lambda>j. s j \<cdot>\<^sub>s f j" in nsum_zeroA)
 apply (rule allI, rule impI)
 apply (simp add:free_generator_def generator_def, frule conjunct1,
        frule_tac x = j and f = f and A = "{j. j \<le> n}" and B = H in
        funcset_mem, simp,
        frule_tac c = "f j" in subsetD[of H "carrier M"], assumption+,
       frule_tac x = j and f = s and A = "{j. j \<le> n}" and B = "{\<zero>\<^bsub>R\<^esub>}" in
       funcset_mem, simp, simp add:sc_0_m)
 apply simp
done

lemma (in Module) unique_expression1:"\<lbrakk>H \<subseteq> carrier M; free_generator R M H;
      s \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R; m \<in> {j. j \<le> n} \<rightarrow> H; 
      inj_on m {j. j \<le> n}; l_comb R M n s m = \<zero>\<rbrakk> \<Longrightarrow> 
                                 \<forall>j\<in>{j. j \<le> n}. s j = \<zero>\<^bsub>R\<^esub>" 
apply (rule ballI)
apply (simp add:free_generator_def, (erule conjE)+)
apply (subgoal_tac "s \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}")
 apply (frule_tac f = s and A = "{j. j \<le> n}" and B = "{\<zero>\<^bsub>R\<^esub>}" and x = j in 
        funcset_mem, simp, simp)
apply blast
done

lemma (in Module) free_gen_coeff_zero:"\<lbrakk>H \<subseteq> carrier M; free_generator R M H;
       h \<in> H; a \<in> carrier R; a \<cdot>\<^sub>s h = \<zero>\<rbrakk> \<Longrightarrow> a = \<zero>\<^bsub>R\<^esub>"
apply (frule unique_expression1[of H "\<lambda>x\<in>{0::nat}. a" 0 "\<lambda>x\<in>{0::nat}. h"],
        assumption+,
       simp,
       simp,
       simp add:inj_on_def,
       simp add:l_comb_def,
       simp)
done

lemma (in Module) unique_expression2:"\<lbrakk>H \<subseteq> carrier M; 
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; s \<in> {j. j \<le> n} \<rightarrow> carrier R\<rbrakk> \<Longrightarrow>
    \<exists>m g t. g \<in> ({j. j \<le> (m::nat)} \<rightarrow> H) \<and> 
            bij_to g {j. j \<le> (m::nat)} (f ` {j. j \<le> n}) \<and> 
            t \<in> {j. j \<le> m} \<rightarrow> carrier R \<and> 
            l_comb R M n s f = l_comb R M m t g" 
apply (cut_tac sc_Ring)
apply (frule Ring.whole_ideal [of "R"])
apply (frule_tac  A = "carrier R" and H = H and s = s and f = f in 
       same_together, assumption+)
apply ((erule bexE)+, erule conjE)
apply (frule_tac f = f and A = "{j. j \<le> n}" in image_sub0,
       frule_tac f = g and A = "{j. j \<le> card (f ` {j. j \<le> n}) - Suc 0}" 
       and B = "f ` {j. j \<le> n}" in extend_fun[of _ _ _ "H"], assumption)
apply (subgoal_tac "bij_to g {j. j \<le> (card (f ` {j. j \<le> n}) - Suc 0)} 
                                  (f ` {j. j \<le> n})")
 apply (simp add:l_comb_def, blast)
apply (simp add:bij_to_def)
apply (cut_tac finite_Collect_le_nat[of n],
        frule finite_imageI[of "{j. j \<le> n}" f])
apply (rule_tac A = "f ` {j. j \<le> n}" and n = "card (f ` {j. j \<le> n}) - 
        Suc 0" and f = g in Nset2finite_inj, assumption)
 using image_Nsetn_card_pos[of f n] apply simp
apply assumption
done

lemma (in Module) unique_expression3_1:"\<lbrakk>H \<subseteq> carrier M; 
      f \<in> {l. l \<le> (Suc n)} \<rightarrow> H; s \<in> {l. l \<le> (Suc n)} \<rightarrow> carrier R; 
      (f (Suc n)) \<notin> f `({l. l \<le> (Suc n)} - {Suc n})\<rbrakk> \<Longrightarrow> 
     \<exists>g m t. g \<in> {l. l \<le> (m::nat)} \<rightarrow> H \<and> 
             inj_on g {l. l \<le> (m::nat)} \<and> 
             t \<in> {l. l \<le> (m::nat)} \<rightarrow> carrier R \<and> 
             l_comb R M (Suc n) s f = 
                 l_comb R M m t g \<and> t m = s (Suc n) \<and> g m = f (Suc n)"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal)
apply (simp add:Nset_pre1)
 apply (subst l_comb_Suc[of H "carrier R" s n f], assumption+)
 apply (frule func_pre[of _ _ H], frule func_pre[of _ _ "carrier R"])
 apply (frule unique_expression2[of H f n s], assumption+)
 apply ((erule exE)+, (erule conjE)+, simp,
        thin_tac "l_comb R M n s f = l_comb R M m t g")
 apply (frule_tac f = g and n = m and A = H and g = "\<lambda>k\<in>{0::nat}. f (Suc n)"
         and m = 0 and B = H in jointfun_hom0,
        simp add:Pi_def, simp)
 apply (frule_tac f = t and n = m and A = "carrier R" and 
        g = "\<lambda>k\<in>{0::nat}. s (Suc n)"  and m = 0 and B = "carrier R" in 
        jointfun_hom0,
        simp add:Pi_def, simp)
 apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n))) 
                       {l. l \<le> Suc m}",
    subgoal_tac "l_comb R M m t g \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        l_comb R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n))) 
                             (jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n)))",
    subgoal_tac "(jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n))) (Suc m) = s (Suc n) \<and>
                 (jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n))) (Suc m) = f (Suc n)",
    simp, blast)
 apply (simp add:jointfun_def sliden_def)
  apply (frule_tac s = t and n = m and f = g and t = "\<lambda>k\<in>{0}. s (Suc n)" and
         m = 0 and g = "\<lambda>k\<in>{0}. f (Suc n)" in l_comb_jointfun_jj[of H 
        "carrier R"], assumption+,
         simp add:Pi_def, simp,
         simp add:Pi_def)
  apply (simp add:l_comb_def, simp add:jointfun_def sliden_def)
  apply (thin_tac "jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n)) \<in> {l. l \<le> Suc m} \<rightarrow> H",
  thin_tac "jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n)) \<in> {l. l \<le> Suc m} \<rightarrow> carrier R",
  thin_tac "t \<in> {j. j \<le> m} \<rightarrow> carrier R", 
  thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R")
 apply (rule_tac f = g and n = m and b = "f (Suc n)" and B = H in jointfun_inj,
        assumption+)
  apply (simp add:bij_to_def)
  apply (unfold bij_to_def, frule conjunct1, fold bij_to_def,
         simp add:surj_to_def)
done
(*
lemma (in Module) unique_expression3_1:"\<lbrakk>H \<subseteq> carrier M; 
      f \<in> {l. l \<le> (Suc n)} \<rightarrow> H; s \<in> {l. l \<le> (Suc n)} \<rightarrow> carrier R; 
      (f (Suc n)) \<notin> f `({l. l \<le> (Suc n)} - {Suc n})\<rbrakk> \<Longrightarrow> 
     \<exists>g m t. g \<in> {l. l \<le> (m::nat)} \<rightarrow> H \<and> 
             inj_on g {l. l \<le> (m::nat)} \<and> 
             t \<in> {l. l \<le> (m::nat)} \<rightarrow> carrier R \<and> 
             l_comb R M (Suc n) s f = l_comb R M m t g \<and> 
              t m = s (Suc n)"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal)
apply (simp add:Nset_pre1)
 apply (subst l_comb_Suc[of H "carrier R" s n f], assumption+)
 apply (frule func_pre[of _ _ H], frule func_pre[of _ _ "carrier R"])
 apply (frule unique_expression2[of H f n s], assumption+)
 apply ((erule exE)+, (erule conjE)+, simp,
        thin_tac "l_comb R M n s f = l_comb R M m t g")
 apply (frule_tac f = g and n = m and A = H and g = "\<lambda>k\<in>{0::nat}. f (Suc n)"
         and m = 0 and B = H in jointfun_hom0,
        rule univar_func_test, rule ballI, simp add:funcset_mem, simp)
 apply (frule_tac f = t and n = m and A = "carrier R" and 
        g = "\<lambda>k\<in>{0::nat}. s (Suc n)"  and m = 0 and B = "carrier R" in 
        jointfun_hom0,
        rule univar_func_test, rule ballI, simp add:funcset_mem, simp)
 apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n))) 
                       {l. l \<le> Suc m}",
    subgoal_tac "l_comb R M m t g \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) =
        l_comb R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n))) 
                             (jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n)))",
    subgoal_tac "(jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n))) (Suc m) = s (Suc n)",
    simp, blast)
 apply (simp add:jointfun_def sliden_def)
  apply (frule_tac s = t and n = m and f = g and t = "\<lambda>k\<in>{0}. s (Suc n)" and
         m = 0 and g = "\<lambda>k\<in>{0}. f (Suc n)" in l_comb_jointfun_jj[of H 
        "carrier R"], assumption+,
         rule univar_func_test, rule ballI, simp add:funcset_mem, simp,
         rule univar_func_test, rule ballI, simp add:funcset_mem)
  apply (simp add:l_comb_def, simp add:jointfun_def sliden_def)
  apply (thin_tac "jointfun m g 0 (\<lambda>k\<in>{0}. f (Suc n)) \<in> {l. l \<le> Suc m} \<rightarrow> H",
  thin_tac "jointfun m t 0 (\<lambda>k\<in>{0}. s (Suc n)) \<in> {l. l \<le> Suc m} \<rightarrow> carrier R",
  thin_tac "t \<in> {j. j \<le> m} \<rightarrow> carrier R", 
  thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R")
 apply (rule_tac f = g and n = m and b = "f (Suc n)" and B = H in jointfun_inj,
        assumption+)
  apply (simp add:bij_to_def)
  apply (unfold bij_to_def, frule conjunct1, fold bij_to_def,
         simp add:surj_to_def)
done     *)

lemma (in Module) unique_expression3_2:"\<lbrakk>H \<subseteq> carrier M; 
      f \<in> {k. k \<le> (Suc n)} \<rightarrow> H; s \<in> {k. k \<le> (Suc n)} \<rightarrow> carrier R; 
      l \<le> (Suc n); (f l) \<notin> f ` ({k. k \<le> (Suc n)} - {l}); l \<noteq> Suc n\<rbrakk> \<Longrightarrow> 
    \<exists>g m t. g \<in> {l. l \<le> (m::nat)} \<rightarrow> H \<and> inj_on g {l. l \<le> (m::nat)} \<and> 
            t \<in> {l. l \<le> m} \<rightarrow> carrier R \<and> 
            l_comb R M (Suc n) s f = l_comb R M m t g \<and> 
             t m = s l \<and> g m = f l"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal)
 apply (subst l_comb_transpos1[of "carrier R" H s n f l], assumption+,
        rule noteq_le_less[of l "Suc n"], assumption+) 
 apply (cut_tac unique_expression3_1[of H "cmp f (transpos l (Suc n))" n 
        "cmp s (transpos l (Suc n))"])
 apply ((erule exE)+, (erule conjE)+, simp)
 apply (subgoal_tac "t m = s l \<and> g m = f l", blast)
 apply (thin_tac "l_comb R M (Suc n) (cmp s (transpos l (Suc n)))
         (cmp f (transpos l (Suc n))) = l_comb R M m t g")
 apply (simp add:cmp_def)
 apply (subst transpos_ij_2[of l "Suc n" "Suc n"], simp+,
        subst transpos_ij_2[of l "Suc n" "Suc n"], simp+) 
 apply (rule Pi_I, simp add:cmp_def,
        frule_tac l = x in transpos_mem[of l "Suc n" "Suc n"], simp,
         assumption+, simp add:Pi_def)
 apply (rule Pi_I, simp add:cmp_def,
        frule_tac l = x in transpos_mem[of l "Suc n" "Suc n"], simp,
         assumption+, simp add:Pi_def)
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in transpos_hom,
           simp, assumption)
 apply (frule cmp_fun_sub_image[of "transpos l (Suc n)" "{i. i \<le> Suc n}" 
       "{i. i \<le> Suc n}" f H "{l. l \<le> Suc n} - {Suc n}"], assumption+)
       apply (rule subsetI, simp)
       apply simp
       apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in transpos_inj,
              simp, assumption+)
       apply (subst injfun_elim_image[of "transpos l (Suc n)" "{i. i \<le> Suc n}"
        "{i. i \<le> Suc n}" "Suc n"], assumption+, simp)
       apply (thin_tac "cmp f (transpos l (Suc n)) ` ({l. l \<le> Suc n} - 
            {Suc n}) = f ` transpos l (Suc n) ` ({l. l \<le> Suc n} - {Suc n})")
       apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in 
              transpos_surjec, simp, assumption+)
       apply (simp add:surj_to_def cmp_def)
    apply (simp add:transpos_ij_2)
done

(*
lemma (in Module) unique_expression3_2:"\<lbrakk>H \<subseteq> carrier M; 
      f \<in> {k. k \<le> (Suc n)} \<rightarrow> H; s \<in> {k. k \<le> (Suc n)} \<rightarrow> carrier R; 
      l \<le> (Suc n); (f l) \<notin> f ` ({k. k \<le> (Suc n)} - {l}); l \<noteq> Suc n\<rbrakk> \<Longrightarrow> 
    \<exists>g m t. g \<in> {l. l \<le> (m::nat)} \<rightarrow> H \<and> inj_on g {l. l \<le> (m::nat)} \<and> 
            t \<in> {l. l \<le> m} \<rightarrow> carrier R \<and> 
            l_comb R M (Suc n) s f = l_comb R M m t g \<and> t m = s l"
apply (cut_tac sc_Ring,
       frule Ring.whole_ideal)
 apply (subst l_comb_transpos1[of "carrier R" H s n f l], assumption+,
        rule noteq_le_less[of l "Suc n"], assumption+) 
 apply (cut_tac unique_expression3_1[of H "cmp f (transpos l (Suc n))" n 
        "cmp s (transpos l (Suc n))"])
 apply ((erule exE)+, (erule conjE)+, simp)
 apply (subgoal_tac "t m = s l", blast)
 apply (thin_tac "l_comb R M (Suc n) (cmp s (transpos l (Suc n)))
         (cmp f (transpos l (Suc n))) = l_comb R M m t g")
 apply (simp add:cmp_def)
 apply (subst transpos_ij_2[of l "Suc n" "Suc n"], assumption+,
        simp, assumption, simp, assumption)
 apply (rule univar_func_test, rule ballI, simp add:cmp_def,
        frule_tac l = x in transpos_mem[of l "Suc n" "Suc n"], simp,
         assumption+, simp add:funcset_mem)
 apply (rule univar_func_test, rule ballI, simp add:cmp_def,
        frule_tac l = x in transpos_mem[of l "Suc n" "Suc n"], simp,
         assumption+, simp add:funcset_mem)
 apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in transpos_hom,
           simp, assumption)
 apply (frule cmp_fun_sub_image[of "transpos l (Suc n)" "{i. i \<le> Suc n}" 
       "{i. i \<le> Suc n}" f H "{l. l \<le> Suc n} - {Suc n}"], assumption+)
       apply (rule subsetI, simp)
       apply simp
       apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in transpos_inj,
              simp, assumption+)
       apply (subst injfun_elim_image[of "transpos l (Suc n)" "{i. i \<le> Suc n}"
        "{i. i \<le> Suc n}" "Suc n"], assumption+, simp)
       apply (thin_tac "cmp f (transpos l (Suc n)) ` ({l. l \<le> Suc n} - 
            {Suc n}) = f ` transpos l (Suc n) ` ({l. l \<le> Suc n} - {Suc n})")
       apply (frule_tac i = l and n = "Suc n" and j = "Suc n" in 
              transpos_surjec, simp, assumption+)
       apply (simp add:surj_to_def cmp_def)
    apply (simp add:transpos_ij_2)
done  *)

lemma (in Module) unique_expression3:
   "\<lbrakk>H \<subseteq> carrier M; f \<in> {k. k \<le> (Suc n)} \<rightarrow> H;
     s \<in> {k. k \<le> (Suc n)} \<rightarrow> carrier R; l \<le> (Suc n);
    (f l) \<notin> f ` ({k. k \<le> (Suc n)} - {l})\<rbrakk> \<Longrightarrow> 
   \<exists>g m t. g \<in> {k. k \<le> (m::nat)} \<rightarrow> H \<and> 
        inj_on g {k. k \<le> m} \<and> 
        t \<in> {k. k \<le> m} \<rightarrow> carrier R \<and> 
        l_comb R M (Suc n) s f = l_comb R M m t g \<and> t m = s l \<and> g m = f l"
apply (case_tac "l = Suc n", simp)
 apply (cut_tac unique_expression3_1[of H f n s], blast,
        assumption+)
 apply (rule unique_expression3_2[of H f n s l], assumption+)
done

lemma (in Module) unique_expression4:"free_generator R M H \<Longrightarrow>
     f \<in> {k. k \<le> (n::nat)} \<rightarrow> H \<and> inj_on f {k. k \<le> n} \<and> 
     s \<in> {k. k \<le> n} \<rightarrow> carrier R \<and> l_comb R M n s f \<noteq> \<zero>  \<longrightarrow> 
(\<exists>m g t. (g \<in> {k. k \<le> m} \<rightarrow> H) \<and> inj_on g {k. k \<le> m} \<and> 
        (g ` {k. k \<le> m} \<subseteq> f ` {k. k \<le> n}) \<and> (t \<in> {k. k \<le> m} \<rightarrow> carrier R) \<and>
        (\<forall>l \<in> {k. k \<le> m}. t l \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> l_comb R M n s f = l_comb R M m t g)"
apply (cut_tac sc_Ring)
apply (frule free_generator_sub[of H])
apply (induct_tac n)
 apply (rule impI, (erule conjE)+)
 apply (frule has_free_generator_nonzeroring[of H])
   apply (frule Ring.whole_ideal,
         frule_tac s = s and n = 0 and f = f in 
             l_comb_mem_linear_span[of "carrier R" H], assumption+)
   apply blast
 apply (simp add:l_comb_def)
 apply (subgoal_tac "f \<in> {j. j \<le> (0::nat)} \<rightarrow> H \<and> 
        inj_on f {j. j \<le> 0} \<and> f ` {j. j \<le> 0} \<subseteq> f ` {0} \<and> 
        s \<in> {j. j \<le> 0} \<rightarrow> carrier R \<and> (\<forall>l \<le> 0. s l \<noteq> \<zero>\<^bsub>R\<^esub>) \<and>  
        s 0 \<cdot>\<^sub>s (f 0) = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (f j)) 0",
        (erule conjE)+, blast)
 apply simp
 apply (rule contrapos_pp, simp+)
 apply (cut_tac m = "f 0" in sc_0_m,
           simp add:Pi_def subsetD, simp)

apply (rule impI) apply (erule conjE)+
 apply (frule func_pre[of _ _ H],
        frule_tac f = f and A = "{k. k \<le> Suc n}" and ?A1.0 = "{k. k \<le> n}" in
        restrict_inj, rule subsetI, simp,
        frule func_pre[of _ _ "carrier R"], simp)
 apply (frule Ring.whole_ideal)
 apply (frule free_generator_sub[of H], 
         simp add:l_comb_Suc[of H "carrier R" s _ f])

 apply (case_tac "s (Suc n) = \<zero>\<^bsub>R\<^esub>", simp)
       apply (frule_tac x = "Suc n" and f = f and A = "{k. k \<le> Suc n}" and
              B = H in funcset_mem, simp,
             frule_tac c = "f (Suc n)" in subsetD[of H "carrier M"], simp)
       apply (frule_tac m = "f (Suc n)" in sc_0_m, simp)
       apply (frule_tac n = n in l_comb_mem[of "carrier R" H s _ f],
               assumption+, simp add:ag_r_zero)
   apply ((erule exE)+, (erule conjE)+)
   apply (frule_tac f = f and A = "{k. k \<le> Suc n}" and B = H and 
          ?A1.0 = "{k. k \<le> n}" and ?A2.0 = "{k. k \<le> Suc n}" in im_set_mono,
          rule subsetI, simp, simp,
          frule_tac A = "g ` {k. k \<le> m}" and B = "f ` {k. k \<le> n}" and 
          C = "f ` {k. k \<le> Suc n}" in subset_trans, assumption+)
   apply blast

  apply (case_tac "l_comb R M n s f = \<zero>\<^bsub>M\<^esub>", simp,
         frule_tac x = "Suc n" and f = s and A = "{k. k \<le> Suc n}" and 
            B = "carrier R" in funcset_mem, simp,
         frule_tac x = "Suc n" and f = f and A = "{k. k \<le> Suc n}" and 
         B = H in funcset_mem, simp,
         frule_tac c = "f (Suc n)" in subsetD[of H "carrier M"], assumption+,
         frule_tac a = "s (Suc n)" and m = "f (Suc n)" in sc_mem, assumption+,
         simp add:ag_l_zero)
  apply (subgoal_tac "(\<lambda>j\<in>{0::nat}. f (Suc n)) \<in> {j. j \<le> (0::nat)} \<rightarrow> H \<and> 
     inj_on (\<lambda>j\<in>{0::nat}. f (Suc n)) {j. j \<le> (0::nat)} \<and> 
     (\<lambda>j\<in>{0::nat}. f (Suc n)) ` {j. j \<le> (0::nat)} \<subseteq>  f  ` {k. k \<le> (Suc n)} \<and> 
      (\<lambda>j\<in>{0::nat}. s (Suc n))\<in> {k. k \<le> 0} \<rightarrow> carrier R \<and> 
      (\<forall>l\<le>0. (\<lambda>j\<in>{0::nat}. s (Suc n)) l \<noteq> \<zero>\<^bsub>R\<^esub>) \<and>
        s (Suc n) \<cdot>\<^sub>s f (Suc n) = 
           l_comb R M 0 (\<lambda>j\<in>{0::nat}. s (Suc n)) (\<lambda>j\<in>{0::nat}. f (Suc n))")
 apply ((erule conjE)+, blast) 
 apply simp
 apply (simp add:l_comb_def)
 
 apply simp
 apply ((erule exE)+, (erule conjE)+, erule exE, (erule conjE)+, simp)
 apply (thin_tac "l_comb R M m t g \<noteq> \<zero>",
        thin_tac "l_comb R M m t g \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) \<noteq> \<zero>",
        thin_tac "l_comb R M n s f = l_comb R M m t g")
 apply (frule_tac f = g and n = m and A = H and g = "\<lambda>j\<in>{0::nat}. f (Suc n)"
        and m = 0 and B = H in jointfun_hom,
        rule Pi_I, simp add:Pi_def,
        frule_tac f = t and n = m and A = "carrier R" and 
         g = "\<lambda>j\<in>{0::nat}. s (Suc n)" and m = 0 and B = "carrier R" in 
         jointfun_hom, simp add:Pi_def, simp)
 apply (subgoal_tac "inj_on (jointfun m g 0 (\<lambda>j\<in>{0}. f (Suc n)))
    {k. k \<le> Suc m} \<and> 
 (jointfun m g 0 (\<lambda>j\<in>{0}. f (Suc n))) ` {k. k \<le> Suc m} \<subseteq> f ` {k. k \<le> Suc n} \<and>
 (\<forall>l \<le> (Suc m). (jointfun m t 0 (\<lambda>j\<in>{0}. s (Suc n))) l \<noteq> \<zero>\<^bsub>R\<^esub>) \<and>
 l_comb R M m t g \<plusminus> s (Suc n) \<cdot>\<^sub>s f (Suc n) =
    l_comb R M (Suc m) (jointfun m t 0 (\<lambda>j\<in>{0}. s (Suc n)))
                            (jointfun m g 0 (\<lambda>j\<in>{0}. f (Suc n)))") 
 apply (erule conjE)+ apply blast

 apply (rule conjI) 
  apply (rule_tac f = g and n = m and b = "f (Suc n)" and B = H in 
         jointfun_inj, assumption+)
  apply (rule contrapos_pp, simp+)   
  apply (frule_tac c = "f (Suc n)" and A = "g ` {k. k \<le> m}" and 
       B = "f ` {k. k \<le> n}" in subsetD, assumption+)

  apply (thin_tac "inj_on f {k. k \<le> n}",
         thin_tac "g ` {k. k \<le> m} \<subseteq> f ` {k. k \<le> n}",
         thin_tac "f (Suc n) \<in> g ` {j. j \<le> m}", simp add:image_def,
         erule exE, erule conjE)
  apply (simp add:inj_on_def,
         drule_tac a = "Suc n" in forall_spec, simp,
         thin_tac "\<forall>x\<le>m. \<forall>y\<le>m. g x = g y \<longrightarrow> x = y",
         thin_tac "\<forall>l\<le>m. t l \<noteq> \<zero>\<^bsub>R\<^esub>",
         drule_tac a = x in forall_spec, simp, simp)

  apply (rule conjI, rule subsetI)
  apply (simp add:image_def, erule exE, erule conjE) 
   apply (case_tac "xa = Suc m", simp add:jointfun_def sliden_def)
   apply (cut_tac n = "Suc n" in Nat.le_refl, blast)
   apply (frule_tac m = xa and n = "Suc m" in noteq_le_less, assumption,
            thin_tac "xa \<le> Suc m",
            frule_tac x = xa and n = "Suc m" in less_le_diff,
            thin_tac "xa < Suc m", simp,
      thin_tac "jointfun m g 0 (\<lambda>j\<in>{0}. f (Suc n)) \<in> {j. j \<le> Suc m} \<rightarrow> H",
  thin_tac "jointfun m t 0 (\<lambda>j\<in>{0}. s (Suc n)) \<in> {j. j \<le> Suc m} \<rightarrow> carrier R",
  simp add:jointfun_def)
  apply (subgoal_tac "g xa \<in> {y. \<exists>x\<le>n. y = f x}", simp, erule exE)
  apply (erule conjE, frule_tac i = xb and j = n and k = "Suc n" in
         le_trans, simp, blast)
  apply (rule_tac c = "g xa" and A = "{y. \<exists>x\<le>m. y = g x}" and 
         B = "{y. \<exists>x\<le>n. y = f x}" in subsetD, assumption+,
         simp, blast)
  apply (rule conjI, rule allI, rule impI)
  apply (case_tac "l = Suc m", simp add:jointfun_def sliden_def)
    apply (frule_tac m = l and n = "Suc m" in noteq_le_less, assumption,
            thin_tac "l \<le> Suc m",
            frule_tac x = l and n = "Suc m" in less_le_diff,
            thin_tac "l < Suc m", simp,
  thin_tac "jointfun m g 0 (\<lambda>j\<in>{0}. f (Suc n)) \<in> {j. j \<le> Suc m} \<rightarrow> H",
  thin_tac "jointfun m t 0 (\<lambda>j\<in>{0}. s (Suc n)) \<in> {j. j \<le> Suc m} \<rightarrow> carrier R",
   simp add:jointfun_def)  
  apply (simp add:l_comb_def,
        subst l_comb_jointfun_jj[of H "carrier R"], assumption+,
        simp add:Pi_def,
        simp add:Pi_def)
  apply (simp add:jointfun_def sliden_def)
done

lemma (in Module) unique_prepression5_0:"\<lbrakk>free_generator R M H; 
       f \<in> {j. j \<le> n} \<rightarrow> H; inj_on f {j. j \<le> n};
       s \<in> {j. j \<le> n} \<rightarrow> carrier R; g \<in> {j. j \<le> m} \<rightarrow> H; 
       inj_on g {j. j \<le> m}; t \<in> {j. j \<le> m} \<rightarrow> carrier R; 
       l_comb R M n s f = l_comb R M m t g;\<forall>j\<le>n. s j \<noteq> \<zero>\<^bsub>R\<^esub>; \<forall>k\<le>m. t k \<noteq> \<zero>\<^bsub>R\<^esub>;
       f n \<notin> g ` {j. j \<le> m}; 0 < n\<rbrakk>  \<Longrightarrow> False" 
apply (cut_tac sc_Ring,
       frule Ring.ring_is_ag,
       frule Ring.whole_ideal,
       frule free_generator_sub[of H])
 apply (cut_tac l_comb_Suc[of H "carrier R" s "n - Suc 0" f],
         simp,
         thin_tac "l_comb R M n s f = l_comb R M (n - Suc 0) s f \<plusminus> s n \<cdot>\<^sub>s f n")
  apply (frule free_generator_sub[of H],
         frule l_comb_mem[of "carrier R" H t m g], assumption+,
         frule l_comb_mem[of "carrier R" H s "n - Suc 0" f], assumption+,
         rule func_pre, simp, rule func_pre, simp,
         cut_tac sc_mem[of "s n" "f n"])
  apply (frule ag_pOp_closed[of "l_comb R M (n - Suc 0) s f" "s n \<cdot>\<^sub>s f n"],
          assumption+,
         frule ag_mOp_closed[of "l_comb R M (n - Suc 0) s f"])
  apply (frule ag_pOp_add_l[of "l_comb R M m t g" "l_comb R M (n - Suc 0) s f \<plusminus> s n \<cdot>\<^sub>s f n" "-\<^sub>a (l_comb R M (n - Suc 0) s f)"], assumption+,
        thin_tac "l_comb R M m t g = l_comb R M (n - Suc 0) s f \<plusminus> s n \<cdot>\<^sub>s f n")
  apply (simp add:ag_pOp_assoc[THEN sym, of "-\<^sub>a (l_comb R M (n - Suc 0) s f)"
         "l_comb R M (n - Suc 0) s f" "s n \<cdot>\<^sub>s f n"],
         simp add:ag_l_inv1 ag_l_zero)
  apply (cut_tac func_pre[of f "n - Suc 0" H],
         cut_tac func_pre[of s "n - Suc 0" "carrier R"])
  apply (frule linear_span_iOp_closedTr2[of "carrier R" "H" f "n - Suc 0" s],
         assumption+)
  apply (simp, 
          thin_tac "-\<^sub>a (l_comb R M (n - Suc 0) s f) =
         l_comb R M (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) f")
  apply (subgoal_tac "(\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) 
         \<in> {j. j \<le> n - Suc 0} \<rightarrow> carrier R")
  apply (simp add:l_comb_add[THEN sym, of "carrier R" H
          "\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)" "n - Suc 0" f t m g],
        thin_tac "l_comb R M m t g \<in> carrier M",
        thin_tac "l_comb R M (n - Suc 0) s f \<in> carrier M",
        thin_tac "l_comb R M (n - Suc 0) s f \<plusminus> s n \<cdot>\<^sub>s f n \<in> carrier M",
        thin_tac "l_comb R M (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) f
         \<in> carrier M")
  apply (frule jointfun_hom[of f "n - Suc 0" H g m H], assumption+,
         frule jointfun_hom[of "\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)" "n - Suc 0"
          "carrier R" t m "carrier R"], assumption+, simp)
 (* to apply unique_expression3_1, we show
     f n \<notin> (jointfun (n - Suc 0) f m g) ` {j. j \<le> n + m} *)
 apply (frule im_jointfun[of f "n - Suc 0" H g m H], assumption+)
 apply (frule unique_expression3_1[of H 
  "jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0::nat}. (f n))"
  "n + m"
  "jointfun (n + m) (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) 
  m t) 0 (\<lambda>x\<in>{0::nat}. -\<^sub>a\<^bsub>R\<^esub> (s n))"])
 apply (rule Pi_I,
        case_tac "x \<le> (n + m)", simp,
        simp add:jointfun_def[of "n+m"], simp add:Pi_def,
        simp add:jointfun_def[of "n+m"] sliden_def, simp add:Pi_def)
  apply (rule Pi_I,
        case_tac "x \<le> (n + m)", simp,
        simp add:jointfun_def[of "n+m"], simp add:Pi_def)
  apply (simp add:jointfun_def[of "n+m"] sliden_def,
         frule Ring.ring_is_ag[of R], rule aGroup.ag_mOp_closed, assumption,
         simp add:Pi_def)
  apply (thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
         thin_tac "t \<in> {j. j \<le> m} \<rightarrow> carrier R",
         thin_tac "\<forall>j\<le>n. s j \<noteq> \<zero>\<^bsub>R\<^esub>",
         thin_tac "\<forall>k\<le>m. t k \<noteq> \<zero>\<^bsub>R\<^esub>",
         thin_tac "l_comb R M (n + m)
          (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t)
          (jointfun (n - Suc 0) f m g) =
         s n \<cdot>\<^sub>s f n",
         thin_tac "s \<in> {j. j \<le> n - Suc 0} \<rightarrow> carrier R")
 apply (thin_tac "(\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x))
         \<in> {j. j \<le> n - Suc 0} \<rightarrow> carrier R",
        thin_tac "jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t
         \<in> {j. j \<le> n + m} \<rightarrow> carrier R")
 apply (simp add:Nset_pre1,
        simp add:im_jointfunTr1[of "n + m" "jointfun (n - Suc 0) f m g" 0 
        "\<lambda>x\<in>{0}. f n"],
        thin_tac "jointfun (n - Suc 0) f m g \<in> {j. j \<le> n + m} \<rightarrow> H",
        thin_tac "jointfun (n - Suc 0) f m g ` {j. j \<le> n + m} =
         f ` {j. j \<le> n - Suc 0} \<union> g ` {j. j \<le> m}",
        simp add:jointfun_def[of "n+m"] sliden_def)
 apply (rule contrapos_pp, simp+, simp add:image_def, erule exE,erule conjE,
        simp add:inj_on_def[of f],
        drule_tac a = n in forall_spec, simp,
        thin_tac "\<forall>xa\<le>m. f x \<noteq> g xa",
        drule_tac a = x in forall_spec,
        rule_tac i = x and j = "n - Suc 0" and k = n in Nat.le_trans,
        assumption+, subst Suc_le_mono[THEN sym], simp,
        simp,
        cut_tac n1 = x and m1 = "x - Suc 0" in 
               Suc_le_mono[THEN sym], simp)

defer
 apply (rule Pi_I, simp,
        rule aGroup.ag_mOp_closed, assumption,
        cut_tac  i = x and j = "n - Suc 0" and k = n in Nat.le_trans,
        assumption, subst Suc_le_mono[THEN sym], simp,
        simp add:Pi_def, simp, simp, simp add:Pi_def,
        simp add:Pi_def,
        simp add:Pi_def subsetD, assumption+, simp, simp)
 apply ((erule exE)+, (erule conjE)+, erule exE, (erule conjE)+) 
 apply (cut_tac l_comb_Suc[of H "carrier R" "jointfun (n + m)
           (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
           (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n))" "n + m"
           "jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)"],
        simp) apply (
       thin_tac "l_comb R M (Suc (n + m))
         (jointfun (n + m)
           (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
           (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)))
         (jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)) =
        l_comb R M ma ta ga")
 apply (subgoal_tac "l_comb R M (n + m)
         (jointfun (n + m)
           (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
           (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)))
         (jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)) \<plusminus>
        jointfun (n + m)
         (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
         (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)) (Suc (n + m)) \<cdot>\<^sub>s
        jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)
         (Suc (n + m)) = \<zero>\<^bsub>M\<^esub>", simp,
       thin_tac "l_comb R M (n + m)
         (jointfun (n + m)
           (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
           (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)))
         (jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)) \<plusminus>
        jointfun (n + m)
         (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
         (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)) (Suc (n + m)) \<cdot>\<^sub>s
        jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)
         (Suc (n + m)) =
        l_comb R M ma ta ga",
       thin_tac "l_comb R M (n + m)
         (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t)
         (jointfun (n - Suc 0) f m g) =
        s n \<cdot>\<^sub>s f n",
       thin_tac "jointfun (n - Suc 0) f m g \<in> {j. j \<le> n + m} \<rightarrow> H",
       thin_tac "jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t
        \<in> {j. j \<le> n + m} \<rightarrow> carrier R",
       thin_tac "jointfun (n - Suc 0) f m g ` {j. j \<le> n + m} =
        f ` {j. j \<le> n - Suc 0} \<union> g ` {j. j \<le> m}")
    apply (simp add:jointfun_def[of "n+m"] sliden_def)
    apply (rotate_tac -3, frule sym, thin_tac "\<zero> = l_comb R M ma ta ga")
    apply (frule_tac s = ta and n = ma and m = ga in unique_expression1[of H],
           assumption+)
    apply (rotate_tac -1, 
           drule_tac x = ma in bspec, simp)
    apply (frule_tac funcset_mem[of s "{j. j \<le> n}" "carrier R" n], simp,
           frule sym, thin_tac "ta ma = -\<^sub>a\<^bsub>R\<^esub> (s n)",
           frule aGroup.ag_inv_inv[of R "s n"], assumption+, simp,
           thin_tac " -\<^sub>a\<^bsub>R\<^esub> (s n) = \<zero>\<^bsub>R\<^esub>",
           rotate_tac -1, frule sym, thin_tac " -\<^sub>a\<^bsub>R\<^esub> \<zero>\<^bsub>R\<^esub> = s n",
           simp add:aGroup.ag_inv_zero[of R])

   apply (thin_tac "l_comb R M (n + m)
         (jointfun (n + m)
           (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
           (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)))
         (jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)) \<plusminus>
        jointfun (n + m)
         (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
         (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)) (Suc (n + m)) \<cdot>\<^sub>s
        jointfun (n + m) (jointfun (n - Suc 0) f m g) 0 (\<lambda>x\<in>{0}. f n)
         (Suc (n + m)) =
        l_comb R M ma ta ga",
        thin_tac "ta ma =
        jointfun (n + m)
         (jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) 0
         (\<lambda>x\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s n)) (Suc (n + m))")
  apply (subst l_comb_jointfun_jj1[of H "carrier R"], assumption+,
         rule Pi_I, simp,
         rule aGroup.ag_mOp_closed, assumption, simp add:Pi_def,
         simp add:Pi_def)
  apply (simp,
        thin_tac "l_comb R M (n + m) (jointfun (n - Suc 0) 
       (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t) (jointfun (n - Suc 0) f m g) =
        s n \<cdot>\<^sub>s f n",
       thin_tac "jointfun (n - Suc 0) f m g \<in> {j. j \<le> n + m} \<rightarrow> H",
       thin_tac "jointfun (n - Suc 0) (\<lambda>x\<in>{j. j \<le> n - Suc 0}. -\<^sub>a\<^bsub>R\<^esub> (s x)) m t
        \<in> {j. j \<le> n + m} \<rightarrow> carrier R",
       thin_tac "jointfun (n - Suc 0) f m g ` {j. j \<le> n + m} =
        f ` {j. j \<le> n - Suc 0} \<union> g ` {j. j \<le> m}")
  apply (simp add:jointfun_def[of "n+m"] sliden_def,
         subst sc_minus_am1[THEN sym],
         simp add:Pi_def, simp add:Pi_def subsetD,
         simp add:ag_r_inv1,  simp add:free_generator_sub) 
  apply (assumption+,
         rule Pi_I,
         case_tac "x \<le> n + m", simp add:jointfun_def[of "n+m"],
         simp add:Pi_def,
         simp add:jointfun_def[of "n+m"] sliden_def,
         rule aGroup.ag_mOp_closed, assumption, simp add:Pi_def,
         rule Pi_I, simp,
          case_tac "x \<le> n+m", simp add:jointfun_def[of "n+m"],
          simp add:Pi_def, 
          simp add:jointfun_def[of "n+m"] sliden_def,
          simp add:Pi_def)
done
   
lemma (in Module) unique_expression5:"\<lbrakk>free_generator R M H; 
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; inj_on f {j. j \<le> n}; 
      s \<in> {j. j \<le> n} \<rightarrow> carrier R; g \<in> {j. j \<le> (m::nat)} \<rightarrow> H; 
      inj_on g {j. j \<le> m}; t \<in> {j. j \<le> m} \<rightarrow> carrier R; 
      l_comb R M n s f = l_comb R M m t g; 
     \<forall>j \<in> {j. j \<le> n}. s j \<noteq> \<zero>\<^bsub>R\<^esub>; \<forall>k \<in> {j. j \<le> m}. t k \<noteq> \<zero>\<^bsub>R\<^esub>\<rbrakk> \<Longrightarrow>
      f ` {j. j \<le> n} \<subseteq> g ` {j. j \<le> m}"
apply (cut_tac sc_Ring, frule Ring.ring_is_ag[of R],
       frule Ring.whole_ideal, 
       frule free_generator_sub[of H]) 
apply (rule contrapos_pp, simp+, simp add:subset_eq)
 apply (erule exE, erule conjE) 
 apply (case_tac "n = 0", simp)
  apply (frule_tac f = t and n = m and A = "carrier R" and 
        g = "\<lambda>k\<in>{0::nat}. -\<^sub>a\<^bsub>R\<^esub> (s 0)"  and m = 0 and B = "carrier R" in 
        jointfun_hom0,
        simp add:Pi_def,
        rule aGroup.ag_mOp_closed, assumption, simp add:Pi_def,
        frule_tac f = g and n = m and A = H and 
        g = "\<lambda>k\<in>{0::nat}. (f 0)" and m = 0 and B = H in 
        jointfun_hom0,
        simp add:Pi_def subsetD,
        simp)
  apply (frule sym, thin_tac "l_comb R M 0 s f = l_comb R M m t g")
  apply (frule_tac n = 0 in l_comb_mem[of "carrier R" H s _ f],
         simp add:free_generator_sub, simp+,
         frule_tac n = m in l_comb_mem[of "carrier R" H t _ g],
         simp add:free_generator_sub, assumption+)
  apply (simp add:ag_eq_diffzero[of "l_comb R M m t g" "l_comb R M 0 s f"],
         simp add:l_comb_def[of R M 0 s f],
         frule free_generator_sub[of H],
          frule_tac c = "f 0" in subsetD[of H "carrier M"], assumption+,
          simp add:sc_minus_am1)
  apply (subgoal_tac "l_comb R M m t g \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> (s 0)) \<cdot>\<^sub>s f 0 = 
          l_comb R M (Suc m) (jointfun m t 0 (\<lambda>k\<in>{0}. (-\<^sub>a\<^bsub>R\<^esub> (s 0))))
          (jointfun m g 0 (\<lambda>k\<in>{0}. f 0))", simp)
  apply (frule_tac f = g and n = m and B = H and b = "f 0" in jointfun_inj,
          assumption+)
  apply (frule unique_expression1[of H "jointfun m t 0 (\<lambda>k\<in>{0}. (-\<^sub>a\<^bsub>R\<^esub> (s 0)))" 
        "Suc m" "jointfun m g 0 (\<lambda>k\<in>{0}. f 0)"], assumption+)
 apply (frule_tac x = "Suc m" in bspec, simp,
        thin_tac "\<forall>j\<in>{j. j \<le> Suc m}. jointfun m t 0 (\<lambda>k\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s 0)) j 
          = \<zero>\<^bsub>R\<^esub>")
  apply (simp add:jointfun_def sliden_def)
  apply (frule aGroup.ag_inv_inv[THEN sym, of R "s 0"], assumption,
         simp add:aGroup.ag_inv_zero)
        
  apply (thin_tac "l_comb R M m t g \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> (s 0)) \<cdot>\<^sub>s f 0 = \<zero>",
         simp del:nsum_suc add:l_comb_def)
  apply (cut_tac l_comb_jointfun_jj[of H "carrier R" t m g "\<lambda>k\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s 0)"
               0 "\<lambda>k\<in>{0}. f 0"], simp,
         thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. jointfun m t 0 (\<lambda>k\<in>{0}. -\<^sub>a\<^bsub>R\<^esub> (s 0)) j \<cdot>\<^sub>s
                   jointfun m g 0 (\<lambda>k\<in>{0}. f 0) j) m =
         \<Sigma>\<^sub>e M (\<lambda>j. t j \<cdot>\<^sub>s g j) m",
         simp add:jointfun_def sliden_def, simp add:free_generator_sub,
         assumption+,
         rule Pi_I, simp,
         rule aGroup.ag_mOp_closed, assumption+,
         simp)
 apply (case_tac "x = n", simp,
        rule unique_prepression5_0[of H f n s g m t], assumption+)
 apply (frule_tac j = x in l_comb_transpos1[of "carrier R" H s "n - Suc 0" f],
        rule subsetI, simp,
        simp+,
        rotate_tac -1, frule sym,
        thin_tac "l_comb R M m t g = 
        l_comb R M n (cmp s (transpos x n)) (cmp f (transpos x n))",
        frule_tac i = x and n = n and j = n in transpos_hom, simp,
           assumption,
        frule_tac i = x and n = n and j = n in transpos_inj, simp,
           assumption+,
        rule_tac f = "cmp f (transpos x n)" and s = "cmp s (transpos x n)" in 
        unique_prepression5_0[of H _ n _ g m t], assumption+,
        simp add:cmp_fun, simp add:cmp_fun, simp add:cmp_inj,
        simp add:cmp_fun, assumption+,
        rule allI, rule impI, simp add:cmp_def,
        frule_tac i = x and n = n and j = n and l = j in transpos_mem,
        simp, assumption+, blast, assumption)
  apply (simp add:cmp_def transpos_ij_2) 
  apply simp
done
 
lemma (in Module) unique_expression6:"\<lbrakk>free_generator R M H;
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; inj_on f {j. j \<le> n}; 
      s \<in> {j. j \<le> n} \<rightarrow> carrier R; 
      g \<in> {j. j \<le> (m::nat)} \<rightarrow> H; inj_on g {j. j \<le> m}; 
      t \<in> {j. j \<le> m} \<rightarrow> carrier R;
      l_comb R M n s f = l_comb R M m t g;
      \<forall>j\<in>{j. j \<le> n}. s j \<noteq> \<zero>\<^bsub>R\<^esub>; \<forall>k\<in> {j. j \<le> m}. t k \<noteq> \<zero>\<^bsub>R\<^esub>\<rbrakk> \<Longrightarrow> 
      f `{j. j \<le> n} = g `  {j. j \<le> m}"
apply (rule equalityI)
apply (rule_tac  H = H and f = f and n = n and s = s and g = g and m = m and 
       t = t in unique_expression5, assumption+)
apply (rule_tac  H = H and f = g and n = m and s = t and g = f and m = n and 
       t = s in unique_expression5, assumption+)
apply (rule sym, assumption, blast, blast)
done

lemma (in Module) unique_expression7_1:"\<lbrakk>free_generator R M H; 
    f \<in> {j. j \<le> (n::nat)} \<rightarrow> H; inj_on f {j. j \<le> n}; 
    s \<in> {j. j \<le> n} \<rightarrow> carrier R; 
    g \<in> {j. j \<le> (m::nat)} \<rightarrow> H; inj_on g {j. j \<le> m}; 
    t \<in> {j. j \<le> m} \<rightarrow> carrier R; 
    l_comb R M n s f = l_comb R M m t g; 
   \<forall>j \<in> {j. j \<le> n}. s j \<noteq> \<zero>\<^bsub>R\<^esub>; \<forall>k\<in>{j. j \<le> m}. t k \<noteq> \<zero>\<^bsub>R\<^esub>\<rbrakk> \<Longrightarrow> n = m"
apply (frule_tac A = "{j. j \<le> n}" and f = f in card_image,
       frule_tac A = "{j. j \<le> m}" and f = g in card_image)
apply (frule_tac H = H and f = f and n = n and s = s and g = g and t = t and 
       m = m in unique_expression6, assumption+)
apply (rotate_tac -3, frule sym, 
       thin_tac "card (f ` {j. j \<le> n}) = card ({j. j \<le> n})")
apply simp
done

lemma (in Module) unique_expression7_2:"\<lbrakk>free_generator R M H;
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> H;  inj_on f {j. j \<le> n};
      s \<in> {j. j \<le> n} \<rightarrow> carrier R; t \<in> {j. j \<le> n} \<rightarrow> carrier R; 
      l_comb R M n s f = l_comb R M n t f\<rbrakk> \<Longrightarrow> (\<forall>l \<in> {j. j \<le> n}. s l = t l)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
 apply (frule free_generator_sub[of H])
 apply (frule l_comb_mem[of "carrier R" H s n f], assumption+,
        frule l_comb_mem[of "carrier R" H t n f], assumption+)
 apply (simp add:ag_eq_diffzero[of "l_comb R M n s f" "l_comb R M n t f"])
 apply (simp add:linear_span_iOp_closedTr2[of "carrier R" H f n t])
 apply (frule l_comb_add1[THEN sym, of "carrier R" H f n s "\<lambda>j\<in>{k. k \<le> n}. -\<^sub>a\<^bsub>R\<^esub> (t j)"],
            assumption+)
       apply (rule Pi_I)
       apply (simp, frule Ring.ring_is_ag[of R],
              rule aGroup.ag_mOp_closed[of R], simp add:Pi_def)
       apply (simp add:Pi_def)
       apply simp
 apply (frule_tac s = "\<lambda>x\<in>{x. x \<le> n}. s x \<plusminus>\<^bsub>R\<^esub> (if x \<le> n then -\<^sub>a\<^bsub>R\<^esub> (t x) else 
        undefined)" in unique_expression1[of H _ n f], assumption+)
  apply (rule Pi_I, simp)
  apply (frule Ring.ring_is_ag[of R], rule aGroup.ag_pOp_closed, assumption,
         simp add:Pi_def,
         rule aGroup.ag_mOp_closed, assumption,
         simp add:Pi_def, assumption+)
  apply (rule allI, rule impI)
  apply (subst aGroup.ag_eq_diffzero[of R],
         simp add:Ring.ring_is_ag,
         simp add:Pi_def, simp add:Pi_def)
 apply (drule_tac x = l in bspec, simp)
  apply simp
done

end
