(*  Title:       A theory of Featherweight Java in Isabelle/HOL
    Author:      Nate Foster <jnfoster at cis.upenn.edu>, 
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>, 2006
    Maintainer:  Nate Foster <jnfoster at cis.upenn.edu>,
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>
    License:     LGPL

  Auxiliary lemmas
*)

section \<open>{\tt FJAux}: Auxiliary Lemmas\<close>

theory FJAux imports FJDefs
begin 

subsection\<open>Non-FJ Lemmas\<close>

subsubsection\<open>Lists\<close>
lemma mem_ith: 
  assumes "ei \<in> set es" 
  shows "\<exists> el er. es = el@ei#er"
  using assms
proof(induct es)
  case Nil thus ?case by auto
next
  case (Cons esh est) 
  { assume "esh = ei" 
    with Cons have ?case by blast
  } moreover {
    assume "esh \<noteq> ei"
    with Cons have "ei \<in> set est" by auto    
    with Cons obtain el er where "esh # est = (esh#el) @ (ei#er)" by auto
    hence ?case by blast }
  ultimately show ?case by blast
qed

lemma ith_mem: "\<And>i. \<lbrakk> i < length es \<rbrakk> \<Longrightarrow> es!i \<in> set es"
proof(induct es)
  case Nil thus ?case by auto
next
  case (Cons h t) thus ?case by(cases "i", auto)
qed   

subsubsection\<open>Maps\<close>

lemma map_shuffle: 
  assumes "length xs = length ys"
  shows "[xs[\<mapsto>]ys,x\<mapsto>y] = [(xs@[x])[\<mapsto>](ys@[y])]"
  using assms
by (induct "xs" "ys" rule:list_induct2) (auto simp add:map_upds_append1)

lemma map_upds_index: 
  assumes "length xs = length As"
  and "[xs[\<mapsto>]As]x = Some Ai"
  shows "\<exists>i.(As!i = Ai) 
         \<and> (i < length As) 
         \<and> (\<forall>(Bs::'c list).((length Bs = length As) 
                            \<longrightarrow> ([xs[\<mapsto>]Bs] x = Some (Bs !i))))" 
  (is "\<exists>i. ?P i xs As" 
   is "\<exists>i.(?P1 i As) \<and> (?P2 i As) \<and> (\<forall>Bs::('c list).(?P3 i xs As Bs))")
  using assms
proof(induct "xs" "As" rule:list_induct2)
  assume "[[][\<mapsto>][]] x = Some Ai"
  moreover have "\<not>[[][\<mapsto>][]] x = Some Ai" by auto
  ultimately show "\<exists>i. ?P i [] []" by contradiction
next
  fix xa xs y ys 
  assume length_xs_ys: "length xs = length ys"
    and IH: "[xs [\<mapsto>] ys] x = Some Ai \<Longrightarrow> \<exists>i. ?P i xs ys"
    and map_eq_Some: "[xa # xs [\<mapsto>] y # ys] x = Some Ai"
  then have map_decomp: "[xa#xs [\<mapsto>] y#ys] = [xa\<mapsto>y] ++ [xs[\<mapsto>]ys]" by fastforce
  show "\<exists>i. ?P i (xa#xs) (y # ys)"
  proof(cases "[xs[\<mapsto>]ys]x")
    case(Some Ai')
    hence "([xa \<mapsto>y] ++ [xs[\<mapsto>]ys]) x = Some Ai'" by(rule map_add_find_right)
    hence P: "[xs[\<mapsto>]ys] x = Some Ai" using map_eq_Some Some by simp
    from IH[OF P] obtain i where 
      R1: "ys ! i = Ai" 
      and R2: "i < length ys" 
      and pre_r3: "\<forall>(Bs::'c list). ?P3 i xs ys Bs" by fastforce
    { fix Bs::"'c list"
      assume length_Bs: "length Bs = length (y#ys)"
      then obtain n where "length (y#ys) = Suc n" by auto
      with length_Bs obtain b bs where Bs_def: "Bs = b#bs" by (auto simp add:length_Suc_conv)
      with length_Bs have "length ys = length bs" by simp
      with pre_r3 have "([xa\<mapsto>b] ++ [xs[\<mapsto>]bs]) x = Some (bs!i)" by(auto simp only:map_add_find_right)
      with pre_r3 Bs_def length_Bs have "?P3 (i+1) (xa#xs) (y#ys) Bs" by simp }
    with R1 R2 have "?P (i+1) (xa#xs) (y#ys)" by auto
    thus ?thesis ..
  next
    case None
    with map_decomp map_eq_Some have "[xa\<mapsto>y] x = Some Ai" by (auto simp only:map_add_SomeD)
    hence ai_def: "y = Ai" and x_eq_xa:"x=xa" by (auto simp only:map_upd_Some_unfold)  
    { fix Bs::"'c list"
      assume length_Bs: "length Bs = length (y#ys)"
      then obtain n where "length (y#ys) = Suc n" by auto
      with length_Bs obtain b bs where Bs_def: "Bs = b#bs" by (auto simp add:length_Suc_conv)
      with length_Bs have "length ys = length bs" by simp
      hence "dom([xs[\<mapsto>]ys]) = dom([xs[\<mapsto>]bs])" by auto
      with None have "[xs[\<mapsto>]bs] x = None" by (auto simp only:domIff)
      moreover from x_eq_xa have sing_map: "[xa\<mapsto>b] x = Some b" by (auto simp only:map_upd_Some_unfold)
      ultimately have "([xa\<mapsto>b] ++ [xs[\<mapsto>]bs]) x = Some b" by (auto simp only:map_add_Some_iff)
      with Bs_def have "?P3 0 (xa#xs) (y#ys) Bs" by simp }
    with ai_def have "?P 0 (xa#xs) (y#ys)" by auto
    thus ?thesis ..
  qed
qed

subsection\<open>FJ Lemmas\<close> 

subsubsection\<open>Substitution\<close>

lemma subst_list1_eq_map_substs : 
  "\<forall>\<sigma>. subst_list1 \<sigma> l = map (substs \<sigma>) l"
   by (induct l, simp_all)

lemma subst_list2_eq_map_substs : 
  "\<forall>\<sigma>. subst_list2 \<sigma> l = map (substs \<sigma>) l"
   by (induct l, simp_all)

subsubsection\<open>Lookup\<close>

lemma lookup_functional:
  assumes "lookup l f = o1"
  and "lookup l f = o2"
  shows "o1 = o2"
using assms by (induct l) auto

lemma lookup_true:
  "lookup l f = Some r \<Longrightarrow> f r"
proof(induct l)
  case Nil thus ?case by simp
next
  case(Cons h t) thus ?case by(cases "f h") (auto simp add:lookup.simps)
qed

lemma lookup_hd:
  "\<lbrakk> length l > 0; f (l!0) \<rbrakk> \<Longrightarrow> lookup l f = Some (l!0)"
by (induct l) auto

lemma lookup_split: "lookup l f = None \<or> (\<exists>h. lookup l f = Some h)"
by (induct l) simp_all

lemma lookup_index:
  assumes "lookup l1 f = Some e" 
  shows " \<And>l2. \<exists>i < (length l1). e = l1!i \<and> ((length l1 = length l2) \<longrightarrow> lookup2 l1 l2 f = Some (l2!i))"
  using assms
proof(induct l1)
  case Nil thus ?case by auto
next
  case (Cons h1 t1)
  { assume asm:"f h1"
    hence "0<length (h1 # t1) \<and> e = (h1 # t1) ! 0" 
      using Cons by (auto simp add:lookup.simps)
    moreover { 
      assume "length (h1 # t1) = length l2"  
      hence "length l2 = Suc (length t1)" by auto
      then obtain h2 t2 where l2_def:"l2 = h2#t2" by (auto simp add: length_Suc_conv)
      hence "lookup2 (h1 # t1) l2 f = Some (l2 ! 0)" using asm by(auto simp add: lookup2.simps)
    }
    ultimately have ?case by auto
  } moreover { 
    assume asm:"\<not> (f h1)"
    hence "lookup t1 f = Some e" 
      using Cons by (auto simp add:lookup.simps)
    then obtain i where 
      "i<length t1" 
      and "e = t1 ! i" 
      and  ih:"(length t1 = length (tl l2) \<longrightarrow> lookup2 t1 (tl l2) f = Some ((tl l2) ! i))" 
      using Cons by blast
    hence "Suc i < length (h1#t1) \<and> e = (h1#t1)!(Suc i)" using Cons by auto
    moreover {
      assume "length (h1 # t1) = length l2"
      hence lens:"length l2 = Suc (length t1)" by auto
      then obtain h2 t2 where l2_def:"l2 = h2#t2" by (auto simp add: length_Suc_conv)
      hence "lookup2 t1 t2 f = Some (t2 ! i)" using ih l2_def lens by auto
      hence "lookup2 (h1 # t1) l2 f = Some (l2!(Suc i))" 
        using asm l2_def by(auto simp add: lookup2.simps)
    }
    ultimately have ?case by auto
  }
  ultimately show ?case by auto
qed

lemma lookup2_index:
  "\<And>l2. \<lbrakk> lookup2 l1 l2 f = Some e; 
  length l1 = length l2 \<rbrakk> \<Longrightarrow> \<exists>i < (length l2). e = (l2!i) \<and> lookup l1 f = Some (l1!i)"
proof(induct l1)
  case Nil thus ?case by auto
next
  case (Cons h1 t1) 
  hence "length l2 = Suc (length t1)" by auto
  then obtain h2 t2 where l2_def:"l2 = h2#t2" by (auto simp add: length_Suc_conv)
  { assume asm:"f h1"
    hence "e = h2" using Cons l2_def by (auto simp add:lookup2.simps)
    hence "0<length (h2#t2) \<and> e = (h2#t2) ! 0 \<and> lookup (h1 # t1) f = Some ((h1 # t1) ! 0)"
      using asm by (auto simp add:lookup.simps)
    hence ?case using l2_def by auto
  } moreover { 
    assume asm:"\<not> (f h1)"
    hence "\<exists>i<length t2. e = t2 ! i \<and> lookup t1 f = Some (t1 ! i)" using Cons l2_def by auto
    then obtain i where "i<length t2 \<and>  e = t2 ! i \<and> lookup t1 f = Some (t1 ! i)" by auto
    hence "(Suc i) < length(h2#t2) \<and> e = ((h2#t2) ! (Suc i)) \<and> lookup (h1#t1) f = Some ((h1#t1) ! (Suc i))" 
      using asm by (force simp add: lookup.simps)
    hence ?case using l2_def by auto
  }
  ultimately show ?case by auto
qed

lemma lookup_append:
  assumes "lookup l f = Some r"
  shows "lookup (l@l') f = Some r"
  using assms by(induct l) auto

lemma method_typings_lookup:
  assumes lookup_eq_Some: "lookup M f = Some mDef"
  and M_ok: "CT \<turnstile>+ M OK IN C"
  shows "CT \<turnstile> mDef OK IN C"
  using lookup_eq_Some M_ok 
proof(induct M)
  case Nil thus ?case by fastforce
next
  case (Cons h t) thus ?case by(cases "f h", auto elim:method_typings.cases simp add:lookup.simps)
qed

subsubsection\<open>Functional\<close>

text \<open>These lemmas prove that several relations are actually functions\<close>

lemma mtype_functional:
  assumes "mtype(CT,m,C) = Cs \<rightarrow> C0"
  and     "mtype(CT,m,C) = Ds \<rightarrow> D0"
  shows "Ds=Cs \<and> D0=C0"
using assms by induct (auto elim:mtype.cases)

lemma mbody_functional:
  assumes mb1: "mbody(CT,m,C) = xs . e0"
  and     mb2: "mbody(CT,m,C) = ys . d0"
  shows "xs = ys \<and> e0 = d0"
using assms by induct (auto elim:mbody.cases)

lemma fields_functional:
  assumes "fields(CT,C) = Cf" 
  and "CT OK" 
  shows "\<And>Cf'. \<lbrakk> fields(CT,C) = Cf'\<rbrakk> \<Longrightarrow> Cf = Cf'"
using assms
proof induct
  case (f_obj CT)
  hence "CT(Object) = None" by (auto elim: ct_typing.cases)
  thus ?case using f_obj by (auto elim: fields.cases)
next
  case (f_class CT C CDef D Cf Dg DgCf DgCf')
  hence f_class_inv: 
    "(CT C = Some CDef) \<and> (cSuper CDef = D) \<and> (cFields CDef = Cf)" 
    and "CT OK" by fastforce+
  hence c_not_obj:"C \<noteq> Object" by (force elim:ct_typing.cases)
  from f_class have flds:"fields(CT,C) = DgCf'" by fastforce
  then obtain Dg' where 
    "fields(CT,D) = Dg'"
    and "DgCf' = Dg' @ Cf" 
    using f_class_inv c_not_obj by (auto elim:fields.cases)
  hence "Dg' = Dg" using f_class by auto
  thus ?case using \<open>DgCf = Dg @ Cf\<close> and \<open>DgCf' = Dg' @ Cf\<close> by force
qed

subsubsection\<open>Subtyping and Typing\<close>

lemma typings_lengths: assumes "CT;\<Gamma> \<turnstile>+ es:Cs" shows "length es = length Cs" 
  using assms by(induct "es" "Cs") (auto elim:typings.cases)

lemma typings_index:
  assumes "CT;\<Gamma> \<turnstile>+ es:Cs" 
  shows "\<And>i. \<lbrakk> i < length es \<rbrakk> \<Longrightarrow> CT;\<Gamma> \<turnstile> (es!i) : (Cs!i)" 
proof -
  have "length es = length Cs" using assms by (auto simp: typings_lengths)
  thus "\<And>i. \<lbrakk> i < length es \<rbrakk> \<Longrightarrow> CT;\<Gamma> \<turnstile> (es!i) : (Cs!i)" 
    using assms
  proof(induct es Cs rule:list_induct2)
    case Nil thus ?case by auto
  next
    case (Cons esh est hCs tCs i)
    thus ?case by(cases i) (auto elim:typings.cases)
  qed
qed


lemma subtypings_index:
  assumes "CT \<turnstile>+ Cs <: Ds"
  shows "\<And>i. \<lbrakk> i < length Cs \<rbrakk> \<Longrightarrow> CT \<turnstile> (Cs!i) <: (Ds!i)"
  using assms
proof induct
  case ss_nil thus ?case by auto
next
  case (ss_cons hCs CT tCs hDs tDs i) 
  thus ?case by(cases "i", auto)
qed

lemma subtyping_append:
  assumes "CT \<turnstile>+ Cs <: Ds"
  and "CT \<turnstile> C <: D"
  shows "CT \<turnstile>+ (Cs@[C]) <: (Ds@[D])"
  using assms
  by (induct rule:subtypings.induct) (auto simp add:subtypings.intros elim:subtypings.cases)

lemma typings_append: 
  assumes "CT;\<Gamma> \<turnstile>+ es : Cs"
  and "CT;\<Gamma> \<turnstile> e : C"
  shows "CT;\<Gamma> \<turnstile>+ (es@[e]) : (Cs@[C])"
proof - 
  have "length es = length Cs" using assms by(simp_all add:typings_lengths)
  thus "CT;\<Gamma> \<turnstile>+ (es@[e]) : (Cs@[C])" using assms
  proof(induct "es" "Cs" rule:list_induct2)
    have "CT;\<Gamma> \<turnstile>+ []:[]" by(simp add:typings_typing.ts_nil)
    moreover from assms have "CT;\<Gamma> \<turnstile> e : C" by simp
    ultimately show "CT;\<Gamma> \<turnstile>+ ([]@[e]) : ([]@[C])" by (auto simp add:typings_typing.ts_cons)
  next
    fix x xs y ys
    assume "length xs = length ys" 
      and IH: "\<lbrakk>CT;\<Gamma> \<turnstile>+ xs : ys; CT;\<Gamma> \<turnstile> e : C\<rbrakk> \<Longrightarrow> CT;\<Gamma> \<turnstile>+ (xs @ [e]) : (ys @ [C])"
      and x_xs_typs: "CT;\<Gamma> \<turnstile>+ (x # xs) : (y # ys)"
      and e_typ: "CT;\<Gamma> \<turnstile> e : C"
    from x_xs_typs have x_typ: "CT;\<Gamma> \<turnstile> x : y" and "CT;\<Gamma> \<turnstile>+ xs : ys" by(auto elim:typings.cases)
    with IH e_typ have "CT;\<Gamma> \<turnstile>+ (xs@[e]) : (ys@[C])" by simp
    with x_typ have "CT;\<Gamma> \<turnstile>+ ((x#xs)@[e]) : ((y#ys)@[C])" by (auto simp add:typings_typing.ts_cons)
    thus "CT;\<Gamma> \<turnstile>+ ((x # xs) @ [e]) : ((y # ys) @ [C])" by(auto simp add:typings_typing.ts_cons)
  qed
qed

lemma ith_typing: "\<And>Cs. \<lbrakk> CT;\<Gamma> \<turnstile>+ (es@(h#t)) : Cs \<rbrakk> \<Longrightarrow> CT;\<Gamma> \<turnstile> h : (Cs!(length es))"
proof(induct "es", auto elim:typings.cases)
qed

lemma ith_subtyping: "\<And>Ds. \<lbrakk> CT \<turnstile>+ (Cs@(h#t)) <: Ds \<rbrakk> \<Longrightarrow> CT \<turnstile> h <: (Ds!(length Cs))"
proof(induct "Cs", auto elim:subtypings.cases)
qed

lemma subtypings_refl: "CT \<turnstile>+ Cs <: Cs" 
by(induct "Cs", auto simp add: subtyping.s_refl subtypings.intros)

lemma subtypings_trans: "\<And>Ds Es. \<lbrakk> CT \<turnstile>+ Cs <: Ds;  CT \<turnstile>+ Ds <: Es \<rbrakk> \<Longrightarrow> CT \<turnstile>+ Cs <: Es"
proof(induct "Cs")
  case Nil thus ?case 
    by (auto elim:subtypings.cases simp add:subtypings.ss_nil)
next
  case (Cons hCs tCs)
  then obtain hDs tDs
    where h1:"CT \<turnstile> hCs <: hDs" and t1:"CT \<turnstile>+ tCs <: tDs" and "Ds = hDs#tDs"
    by (auto elim:subtypings.cases)
  then obtain hEs tEs
    where h2:"CT \<turnstile> hDs <: hEs" and t2:"CT \<turnstile>+ tDs <: tEs" and "Es = hEs#tEs" 
    using Cons by (auto elim:subtypings.cases)
  moreover from subtyping.s_trans[OF h1 h2] have "CT \<turnstile> hCs <: hEs" by fastforce
  moreover with t1 t2 have "CT \<turnstile>+ tCs <: tEs" using Cons by simp_all
  ultimately show ?case by (auto simp add:subtypings.intros)
qed

lemma ith_typing_sub: 
  "\<And>Cs. \<lbrakk> CT;\<Gamma> \<turnstile>+ (es@(h#t)) : Cs; 
     CT;\<Gamma> \<turnstile> h' : Ci'; 
     CT \<turnstile> Ci' <: (Cs!(length es)) \<rbrakk>
  \<Longrightarrow> \<exists>Cs'. (CT;\<Gamma> \<turnstile>+ (es@(h'#t)) : Cs' \<and> CT \<turnstile>+ Cs' <: Cs)"
proof(induct es)
case Nil
 then obtain hCs tCs 
   where ts: "CT;\<Gamma> \<turnstile>+ t : tCs"
   and Cs_def: "Cs = hCs # tCs" by(auto elim:typings.cases)
 from Cs_def Nil have "CT \<turnstile> Ci' <: hCs" by auto
 with Cs_def have "CT \<turnstile>+ (Ci'#tCs) <: Cs" by(auto simp add:subtypings.ss_cons subtypings_refl)
 moreover from ts Nil have "CT;\<Gamma> \<turnstile>+ (h'#t) : (Ci'#tCs)" by(auto simp add:typings_typing.ts_cons)
 ultimately show ?case by auto
next
case (Cons eh et)
then obtain hCs tCs
  where "CT;\<Gamma> \<turnstile> eh : hCs" 
  and "CT;\<Gamma> \<turnstile>+ (et@(h#t)) : tCs"
  and Cs_def: "Cs = hCs # tCs"
  by(auto elim:typings.cases)
moreover with Cons obtain tCs'
  where "CT;\<Gamma> \<turnstile>+ (et@(h'#t)) : tCs'"
  and "CT \<turnstile>+ tCs' <: tCs"
  by auto
ultimately have 
  "CT;\<Gamma> \<turnstile>+ (eh#(et@(h'#t))) : (hCs#tCs')" 
  and "CT \<turnstile>+ (hCs#tCs') <: Cs"
  by(auto simp add:typings_typing.ts_cons subtypings.ss_cons subtyping.s_refl)
thus ?case by auto
qed
   
lemma mem_typings: 
  "\<And>Cs. \<lbrakk> CT;\<Gamma> \<turnstile>+ es:Cs; ei \<in> set es\<rbrakk> \<Longrightarrow> \<exists>Ci. CT;\<Gamma> \<turnstile> ei:Ci"
proof(induct es)
  case Nil thus ?case by auto
next
  case (Cons eh et) thus ?case 
    by(cases "ei=eh", auto elim:typings.cases)
qed

lemma typings_proj: 
  assumes "CT;\<Gamma> \<turnstile>+ ds : As"
      and "CT \<turnstile>+ As <: Bs" 
      and "length ds = length As" 
      and "length ds = length Bs" 
      and "i < length ds" 
    shows "CT;\<Gamma> \<turnstile> ds!i : As!i" and "CT \<turnstile> As!i <: Bs!i"
  using assms by (auto simp add:typings_index subtypings_index)

lemma subtypings_length: 
  "CT \<turnstile>+ As <: Bs \<Longrightarrow> length As = length Bs" 
  by(induct rule:subtypings.induct) simp_all

lemma not_subtypes_aux: 
  assumes "CT \<turnstile> C <: Da" 
  and "C \<noteq> Da" 
  and "CT C = Some CDef" 
  and "cSuper CDef = D"
  shows "CT \<turnstile> D <: Da"
  using assms
by (induct rule:subtyping.induct) (auto intro:subtyping.intros) 

lemma not_subtypes:
  assumes "CT \<turnstile> A <: C"
  shows "\<And>D. \<lbrakk> CT \<turnstile> D \<not><: C;  CT \<turnstile> C \<not><: D\<rbrakk> \<Longrightarrow> CT \<turnstile> A \<not><: D"
  using assms
proof(induct rule:subtyping.induct)
  case s_refl thus ?case by auto
next 
  case (s_trans CT C D E Da)
  have da_nsub_d:"CT \<turnstile> Da \<not><: D"
  proof(rule ccontr)
    assume "\<not> CT \<turnstile> Da \<not><: D"
    hence da_sub_d:"CT \<turnstile> Da <: D" by auto
    have d_sub_e:"CT \<turnstile> D <: E" using s_trans by fastforce
    thus "False" using s_trans by (force simp add:subtyping.s_trans[OF da_sub_d d_sub_e])
  qed 
  have d_nsub_da:"CT \<turnstile> D \<not><: Da" using s_trans by auto
  from da_nsub_d d_nsub_da s_trans show "CT \<turnstile> C \<not><: Da" by auto
next
  case (s_super CT C CDef D Da)
  have "C \<noteq> Da" proof(rule ccontr)
    assume "\<not> C \<noteq> Da"
    hence "C = Da" by auto 
    hence "CT \<turnstile> Da <: D" using s_super by(auto simp add: subtyping.s_super)
    thus "False" using s_super by auto
  qed
  thus ?case using s_super by (auto simp add: not_subtypes_aux)
qed

subsubsection\<open>Sub-Expressions\<close>

lemma isubexpr_typing: 
  assumes "e1 \<in> isubexprs(e0)"
  shows "\<And>C. \<lbrakk> CT;Map.empty \<turnstile> e0 : C \<rbrakk> \<Longrightarrow> \<exists>D. CT;Map.empty \<turnstile> e1 : D"
using assms
  by (induct rule:isubexprs.induct) (auto elim:typing.cases simp add:mem_typings)

lemma subexpr_typing: 
  assumes "e1 \<in> subexprs(e0)"
  shows "\<And>C. \<lbrakk> CT;Map.empty \<turnstile> e0 : C \<rbrakk> \<Longrightarrow> \<exists>D. CT;Map.empty \<turnstile> e1 : D"
using assms
  by (induct rule:rtrancl.induct) (auto, force simp add:isubexpr_typing)

lemma isubexpr_reduct: 
  assumes "d1 \<in> isubexprs(e1)"
  shows "\<And>d2. \<lbrakk> CT \<turnstile> d1 \<rightarrow> d2 \<rbrakk> \<Longrightarrow> \<exists>e2. CT \<turnstile> e1 \<rightarrow> e2"
using assms mem_ith
  by induct
    (auto elim:isubexprs.cases intro:reduction.intros,
      force intro:reduction.intros, 
      force intro:reduction.intros)

lemma subexpr_reduct: 
  assumes "d1 \<in> subexprs(e1)"
  shows "\<And>d2. \<lbrakk> CT \<turnstile> d1 \<rightarrow> d2 \<rbrakk> \<Longrightarrow> \<exists>e2. CT \<turnstile> e1 \<rightarrow> e2"
using assms
  by (induct rule:rtrancl.induct) (auto, force simp add: isubexpr_reduct)

end 
