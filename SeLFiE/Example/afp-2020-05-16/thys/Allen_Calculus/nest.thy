(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)


theory nest

imports 
    Main  jointly_exhaustive examples
    "HOL-Eisbach.Eisbach_Tools"

begin

section \<open>Nests\<close>
text\<open>Nests are sets of intervals that share a meeting point. We define relation before between nests that give the ordering properties of points.\<close>

subsection \<open>Definitions\<close>

type_synonym 'a nest = "'a set"

definition (in arelations) BEGIN :: "'a \<Rightarrow> 'a nest" 
where "BEGIN i  = {j | j. (j,i) \<in> ov \<union> s \<union> m \<union> f^-1 \<union> d^-1 \<union> e \<union> s^-1}"

definition (in arelations) END :: "'a \<Rightarrow> 'a nest" 
where "END i  = {j | j. (j,i) \<in> e \<union> ov^-1 \<union> s^-1 \<union> d^-1 \<union> f \<union> f^-1 \<union> m^-1}"

definition (in arelations) NEST ::"'a nest \<Rightarrow> bool"
where "NEST S \<equiv> \<exists>i. \<I> i \<and> (S = BEGIN i \<or> S = END i)"

definition (in arelations) before :: "'a nest \<Rightarrow> 'a nest \<Rightarrow> bool" (infix "\<lless>" 100)
where "before N M \<equiv> NEST N \<and> NEST M \<and> (\<exists>n m. \<^cancel>\<open>\<I> m \<and> \<I> n \<and>\<close> n \<in> N \<and> m \<in> M \<and> (n,m) \<in> b)"

subsection \<open>Properties of Nests\<close>

lemma intv1:
assumes "\<I> i" 
shows "i \<in> BEGIN i"
unfolding BEGIN_def
by (simp add:e assms)

lemma intv2:
assumes "\<I> i" 
shows "i \<in> END i"
unfolding END_def
by (simp add: e assms)

lemma NEST_nonempty:
assumes "NEST S"
shows "S \<noteq> {}" 
using assms unfolding NEST_def 
by (insert intv1 intv2, auto)

lemma NEST_BEGIN:
assumes "\<I> i" 
shows "NEST (BEGIN i)"
using NEST_def assms by auto

lemma NEST_END:
assumes "\<I> i" 
shows "NEST (END i)"
using NEST_def assms by auto

lemma before:
assumes a:"\<I> i" 
shows "BEGIN i \<lless> END i" 
proof -
  
    obtain p where pi:"(p,i) \<in> m"
    using  a M3 m by blast
    then have p:"p \<in> BEGIN i" using BEGIN_def by auto

    obtain q where qi:"(q,i) \<in> m^-1" 
    using a M3 m by blast
    then have q:"q \<in> END i" using END_def by auto

    from pi qi have c1:"(p,q) \<in> b" using b  m
    by blast 

    with  c1 p q assms show ?thesis  by (auto simp:NEST_def  before_def)

qed

lemma  meets:
fixes i j
 assumes "\<I> i" and "\<I> j" 
shows "(i,j) \<in> m = ((END i) = (BEGIN j))" 
proof 
  assume ij:"(i,j) \<in> m" then have ibj:"i \<in> (BEGIN j)" unfolding BEGIN_def by auto
  from ij have ji:"(j,i) \<in> m^-1" by simp
  then have jeo:"j \<in> (END i)" unfolding END_def by simp
  show "((END i) = (BEGIN j))"
  proof 
      {fix x::"'a" assume a:"x \<in> (END i)"
      then have asimp:"(x,i) \<in> e \<union>  ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> m\<inverse> \<union> f^-1"
      unfolding END_def by auto
      then have "x \<in> (BEGIN j)" using ij eovisidifmifiOm
      by (auto simp:BEGIN_def)     
      }
      thus conc1:"END i \<subseteq> BEGIN j" by auto
   next
     {fix x assume b:"x \<in> (BEGIN j)"
     then have bsimp:"(x,j) \<in> ov \<union> s\<union> m  \<union> f^-1 \<union> d^-1 \<union> e \<union> s^-1"
     unfolding BEGIN_def by auto
     then have "x \<in> (END i)" using ij ovsmfidiesiOmi
     by (auto simp:END_def)
     }thus conc2:"BEGIN j \<subseteq> END i" by auto
  qed
next
  assume a0:"END (i::'a) = BEGIN (j::'a)" show "(i,j) \<in> m"
  proof (rule ccontr)
     assume a:"(i,j) \<notin> m" then have "\<not>i\<parallel>j" using m by auto
     from a have "(i,j) \<in> b  \<union> ov  \<union> s \<union> d \<union> f^-1 \<union> e \<union> f  \<union> s^-1  \<union> d^-1 \<union> ov^-1 \<union> m^-1  \<union> b^-1" using assms JE by auto
     thus False
     proof (auto)
       {assume ij:"(i,j) \<in> e" 
        obtain p where ip:"i\<parallel>p" using M3 assms(1)  by auto
        then  have pi:"(p,i)\<in> m^-1" using m by auto
        then have "p \<in> END i" using END_def by auto
        with a0 have pj:"p \<in> (BEGIN j) " by auto
        from ij pi have "(p,j) \<in> m^-1"  by (simp add: e)
        with pj show   ?thesis
        apply (auto simp:BEGIN_def)
        using m_rules by auto[7] }
       next
       {assume ij: "(j,i) \<in> m" 
        obtain p where ip:"i\<parallel>p" using M3  assms(1) by auto
        then  have pi:"(p,i)\<in> m^-1" using m by auto
        then have "p \<in> END i" using END_def by auto
        with a0 have pj:"p \<in> (BEGIN j) " by auto
        from ij have "(i,j) \<in> m^-1" by simp
        with  pi have "(p,j) \<in> b^-1" using cmimi  by auto
        with pj show   ?thesis
        apply (auto simp:BEGIN_def)
          using b_rules by auto
        }

       next 

       {assume ij:"(i,j)\<in> b"
        have ii:"(i,i)\<in>e" and "i \<in> END i" using assms  intv2 e by auto
        with a0 have j:"i \<in> BEGIN j" by simp
        with ij  show   ?thesis 
        apply (auto simp:BEGIN_def)
          using b_rules by auto
         }
       
        next 

        { assume ji:"(j,i) \<in> b" then have ij:"(i,j) \<in> b^-1" by simp
          have ii:"(i,i)\<in>e" and "i \<in> END i" using assms intv2 e by auto
          with a0 have j:"i \<in> BEGIN j" by simp
          with ij  show   ?thesis 
          apply (auto simp:BEGIN_def)
            using b_rules by auto}
        
        next

        {assume ij:"(i,j)\<in>ov"
         then obtain u v::"'a" where iu:"i\<parallel>u" and uv:"u\<parallel>v" and uv:"u\<parallel>v" using ov by blast
         from iu have "u \<in> END i" using m END_def by auto
         with a0 have u:"u \<in> BEGIN j" by simp
         from iu have "(u,i) \<in> m^-1" using m by auto
         with ij have uj:"(u,j) \<in> ov^-1 \<union> d \<union> f" using covim by auto
         show ?thesis using u uj 
         apply (auto simp:BEGIN_def)
           using ov_rules eovi apply auto[9]
            using s_rules apply auto[2]
              using d_rules apply auto[5]
                using f_rules by auto[5]
        }

        next 
        
        {assume "(j,i) \<in> ov" then have  ij:"(i,j)\<in>ov^-1" by simp let ?p = i 
        from ij have pi:"(?p, i) \<in> e" by (simp add:e)
        from ij have pj:"(?p,j) \<in> ov^-1" by simp
        from pi have "?p \<in> END i" using END_def by auto
        with a0 have "?p \<in> (BEGIN j) " by auto
        with pj show ?thesis 
        apply (auto simp:BEGIN_def)
          using ov_rules by auto
        }
        next
        {assume ij:"(i,j) \<in> s" 
         then obtain p q t where ip:"i\<parallel>p" and pq:"p\<parallel>q" and  jq:"j\<parallel>q" and ti:"t\<parallel>i" and tj:"t\<parallel>j" using s by blast
         from ip have "(p,i) \<in> m^-1" using m by auto
         then have "p \<in> END i" using END_def by auto
         with a0 have p:"p \<in> BEGIN j" by simp
         from ti ip pq tj jq have "(p,j) \<in> f" using f by blast
         with p show ?thesis 
         apply (auto simp:BEGIN_def)
           using f_rules by auto
            
         }
         next
         {assume "(j,i) \<in> s" then have  ij:"(i,j) \<in> s^-1" by simp
          then obtain u v where ju:"j\<parallel>u" and uv:"u\<parallel>v" and iv:"i\<parallel>v" using s by blast
          from iv have "(v,i) \<in> m^-1" using m by blast
          then have "v \<in> END i" using END_def by auto
          with a0 have v:"v \<in> BEGIN j" by simp
          from ju uv have "(v,j) \<in> b^-1" using b by auto
          with v show ?thesis 
          apply (auto simp:BEGIN_def)
            using b_rules by auto}
         next
         {assume ij:"(i,j) \<in> f"
          have "(i,i) \<in> e" and "i \<in> END i" 
          by (simp add: e)  (auto simp: assms intv2 )
          with a0 have "i \<in> BEGIN j" by simp
          with ij show ?thesis 
          apply (auto simp:BEGIN_def)
           using f_rules by auto 
         }
         next
         {assume "(j,i) \<in> f" then have "(i,j)\<in>f^-1" by simp
          then obtain u where ju:"j\<parallel>u" and iu:"i\<parallel>u" using f by auto
          then have ui:"(u,i) \<in> m^-1" and "u \<in> END i"  
          apply (simp add: converse.intros m)
          using END_def iu m by auto
          with a0 have ubj:"u \<in> BEGIN j" by simp
          from ju have "(u,j) \<in> m^-1"  by (simp add: converse.intros m)
          with ubj show  ?thesis 
          apply (auto simp:BEGIN_def)
            using m_rules by auto
         }
         next
         {assume ij:"(i,j) \<in> d" then 
          have "(i,i) \<in> e" and "i \<in> END i" using assms e by (blast, simp add:  intv2)
          with a0 have "i \<in> BEGIN j" by simp
          with ij show ?thesis 
          apply (auto simp:BEGIN_def)
            using d_rules by auto}
          next
          {assume ji:"(j,i) \<in> d" then have "(i,j) \<in> d^-1" using d by simp
           then obtain u v where ju:"j\<parallel>u" and uv:"u\<parallel>v" and iv:"i\<parallel>v" using d using ji by blast
           then have "(v,i) \<in> m^-1" and "v \<in> END i" using m END_def by auto
           with a0 ju uv have  vj:"(v,j) \<in> b^-1" and  "v \<in> BEGIN j" using b by auto
           with vj show ?thesis 
           apply (auto simp:BEGIN_def)
             using b_rules by auto}
          
        qed
    qed
qed


lemma starts:
fixes i j
assumes "\<I> i" and "\<I> j" 
shows "((i,j) \<in> s \<union> s^-1 \<union> e) = (BEGIN i = BEGIN j)"
proof 
   assume a3:"(i,j) \<in> s \<union> s^-1 \<union> e" show "BEGIN i = BEGIN j"
   proof -
    { fix x assume "x \<in> BEGIN i" then have "(x,i) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
    hence "x \<in> BEGIN j" using a3 ovsmfidiesiOssie
    by (auto simp:BEGIN_def)
    } note c1 = this

    { fix x assume "x \<in> BEGIN j" then have xj:"(x,j) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
    then have "x \<in> BEGIN i" 
    apply (insert converseI[OF a3] xj)
    apply (subst (asm) converse_Un)+
    apply (subst (asm) converse_converse)
    using ovsmfidiesiOssie  
    by (auto simp:BEGIN_def)
    } note c2 = this

    from c1 have "BEGIN i \<subseteq> BEGIN j" by auto
    moreover with c2 have "BEGIN j \<subseteq> BEGIN i" by auto
    ultimately show ?thesis by auto  
 qed
next
   assume a4:"BEGIN i = BEGIN j"
   with assms have "i \<in> BEGIN j" and "j \<in> BEGIN i" using intv1 by auto
   then have ij:"(i,j) \<in> ov \<union> s \<union> m \<union> f^-1 \<union> d^-1 \<union> e \<union> s^-1" and ji:"(j,i) \<in>  ov \<union> s \<union> m \<union> f^-1 \<union> d^-1 \<union> e \<union> s^-1"
   unfolding BEGIN_def by auto
   then have ijov:"(i,j) \<notin> ov"  
    apply auto
    using ov_rules  by auto
   
   from ij ji have ijm:"(i,j) \<notin> m"  
   apply (simp_all, elim disjE, simp_all)
    using ov_rules apply auto[13]
      using s_rules apply auto[11]
        using m_rules apply auto[9]
          using f_rules apply auto[7]
            using d_rules apply auto[5]
              using m_rules by auto[4]

   from ij ji have  ijfi:"(i,j) \<notin> f^-1"  
   apply (simp_all, elim disjE, simp_all)
    using ov_rules apply auto[13]
     using s_rules apply auto[11]
      using m_rules apply auto[9]
          using f_rules apply auto[7]
            using d_rules apply auto[5]
              using f_rules by auto[4]

   from ij ji have  ijdi:"(i,j) \<notin> d^-1"  
   apply (simp_all, elim disjE, simp_all)
    using ov_rules apply auto[13]
     using s_rules apply auto[11]
      using m_rules apply auto[9]
          using f_rules apply auto[7]
            using d_rules apply auto[5]
              using d_rules by auto[4]

   from ij ijm ijov ijfi ijdi show "(i, j) \<in> s \<union> s\<inverse> \<union> e" by auto 

qed

lemma xj_set:"x \<in> {a |a. (a, j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>} = ((x,j) \<in>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>)"
by blast

lemma ends:
fixes i j
assumes "\<I> i" and "\<I> j"
shows "((i,j) \<in> f \<union> f^-1 \<union> e) = (END i = END j)"
proof 
   assume a3:"(i,j) \<in> f \<union> f^-1 \<union> e" show "END i = END j"
   proof -
    { fix x assume "x \<in> END i" then have "(x,i) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
      then have "x \<in> END j" using a3 unfolding END_def 
      apply (subst xj_set)
      using ceovisidiffimi_ffie_simp by simp
     } note c1 =this

    { fix x assume "x \<in> END j" then have "(x,j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
      then have "x \<in> END i" using a3 unfolding END_def  
      by (metis Un_iff ceovisidiffimi_ffie_simp converse_iff eei mem_Collect_eq)  
     }  note c2 = this

    from c1 have "END i \<subseteq> END j" by auto
    moreover with c2 have "END j \<subseteq> END i" by auto
    ultimately show ?thesis by auto  
  qed (*} note conc = this *)
  next
  assume a4:"END i = END j"
  with assms have "i \<in> END j" and "j \<in> END i" using intv2 by auto
  then have ij:"(i,j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" and ji:"(j,i) \<in>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>"
  unfolding END_def by auto
  then  have ijov:"(i,j) \<notin> ov^-1"  
  apply (simp_all, elim disjE, simp_all)
   using eov es ed efi ef em eov  apply auto[13] 
    using ov_rules apply auto[11]
     using s_rules apply auto[9]
      using d_rules apply auto[7]
        using f_rules apply auto[8]
          using movi by auto
   
  from ij ji have  ijm:"(i,j) \<notin> m^-1"  
  apply (simp_all, elim disjE, simp_all)
    using m_rules by auto

  from ij ji have  ijfi:"(i,j) \<notin> s^-1"  
  apply (simp_all, elim disjE, simp_all)
    using s_rules by auto

  from ij ji have  ijdi:"(i,j) \<notin> d^-1"  
  apply (simp_all, elim disjE, simp_all)
    using d_rules by auto

  from ij ijm ijov ijfi ijdi  show "(i, j) \<in> f \<union> f\<inverse> \<union> e"  by auto
qed

lemma before_irrefl:
fixes a
shows "\<not> a \<lless> a" 
proof (rule ccontr, auto)
  assume a0:"a \<lless> a"
  then have "NEST a"  unfolding before_def by auto
  then obtain i where   i:"a = BEGIN i \<or> a = END i" unfolding NEST_def by auto
  from i show False
  proof
      assume "a = BEGIN i"
      with a0 have "BEGIN i \<lless> BEGIN i" by simp
      then obtain p q where "p\<in> BEGIN i" and "q \<in> BEGIN i" and b:"(p,q) \<in> b" unfolding before_def by auto
      then  have a1:"(p,i) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" and a2:"(i,q) \<in> ov^-1 \<union> s^-1 \<union> m^-1 \<union> f \<union> d \<union> e \<union> s" unfolding BEGIN_def  
      apply auto 
      using eei apply fastforce
      by (simp add: e)+
      with b show False 
      using piiq[of p i q] 
      apply auto
        using  b_rules using disjoint_iff_not_equal by auto
      next
      assume "a = END i"
      with a0 have "END i \<lless> END i" by simp
      then obtain p q where "p\<in> END i" and "q \<in> END i" and b:"(p,q) \<in> b" unfolding before_def by auto
      then  have a1:"(p,i) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" and a2:"(q,i) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def  
      by auto 
      with b show False
      apply (subst (asm) converse_iff[THEN sym])
      using cbi_alpha1ialpha4mi neq_bi_alpha1ialpha4mi relcomp.relcompI subsetCE by blast        
     qed
qed

lemma BEGIN_before:
fixes i j
assumes "\<I> i" and "\<I> j" 
shows "BEGIN i \<lless> BEGIN j = ((i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>)"
proof 
    
     assume a3:"BEGIN i \<lless> BEGIN j"
     from a3 obtain p q where pa:"p \<in> BEGIN i" and qc:"q \<in> BEGIN j" and pq:"(p,q) \<in> b" unfolding before_def by auto
     then obtain r where "p\<parallel>r" and "r\<parallel>q" using b by auto
     then have pr:"(p,r) \<in> m" and rq:"(r,q) \<in> m" using m by auto
     from pa  have pi:"(p,i) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
     moreover with pr have "(r,p) \<in> m^-1" by simp
     ultimately have "(r,i) \<in> d \<union> f \<union> ov^-1 \<union> e \<union> f^-1 \<union> m^-1 \<union> b^-1 \<union> s \<union> s^-1"
     using cmiov cmis cmim cmifi cmidi  cmisi
     apply ( simp_all,elim disjE, auto)
        by (simp add: e)
     

     then have ir:"(i,r) \<in> d^-1 \<union> f^-1 \<union> ov \<union> e \<union> f \<union> m \<union> b \<union> s^-1 \<union> s" 
     by (metis (mono_tags, lifting) converseD converse_Un converse_converse eei)

     from qc  have "(q,j) \<in>  ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
     with rq have rj:"(r,j) \<in> b \<union> s \<union> m "
     using m_ovsmfidiesi using contra_subsetD relcomp.relcompI by blast
      
     with ir have c1:"(i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> \<union> d \<union> e \<union> s \<union> s\<inverse>"
     using difibs by blast
     {assume "(i,j) \<in> s\<or> (i,j)\<in>s^-1 \<or> (i,j) \<in> e" then have "BEGIN i = BEGIN j" 
      using starts Un_iff assms(1) assms(2) by blast
      with a3 have False  by (simp add: before_irrefl)}

      from c1 have c1':"(i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> \<union> d " 
      using \<open>(i, j) \<in> s \<or> (i, j) \<in> s\<inverse> \<or> (i, j) \<in> e \<Longrightarrow> False\<close> by blast

     {assume "(i,j) \<in> d" with pi have "(p,j) \<in> e \<union>  s \<union> d \<union> ov \<union> ov^-1 \<union> s^-1 \<union> f \<union> f^-1  \<union> d^-1"
      using ovsmfidiesi_d using relcomp.relcompI subsetCE by blast
      with pq have "(q,j) \<in>  b^-1 \<union> d \<union> f \<union> ov^-1 \<union> m^-1"
      apply (subst (asm) converse_iff[THEN sym])
      using cbi_esdovovisiffidi by blast
      with qc have False unfolding BEGIN_def 
      apply (subgoal_tac "(q, j) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>")
        prefer 2
        apply simp 
          using neq_beta2i_alpha2alpha5m by auto
      }

     with c1' show "((i, j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>)"   by auto  
   next
      assume "(i, j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>"
      then show "BEGIN i \<lless> BEGIN j"
      proof  ( simp_all,elim disjE, simp_all)
        assume "(i,j) \<in> b" thus ?thesis using intv1  using before_def NEST_BEGIN assms by metis
        next
        assume iu:"(i,j) \<in> m" 
        obtain l where li:"(l,i) \<in> m" using M3 m meets_wd assms by blast
        with iu have "(l,j) \<in> b" using cmm by auto
        moreover from li  have "l \<in> (BEGIN i)" using BEGIN_def by auto
        ultimately show ?thesis using intv1  before_def NEST_BEGIN assms by blast
        next
        assume iu:"(i,j) \<in> ov"
        obtain l where li:"(l,i) \<in> m" using M3 m meets_wd assms by blast
        with iu have "(l,j) \<in> b" using cmov by auto
        moreover from li have "l \<in> (BEGIN i)" using BEGIN_def by auto
        ultimately show ?thesis using intv1 before_def NEST_BEGIN assms by blast
        next
        assume iu:"(j,i) \<in> f" 
        obtain l where li:"(l,i) \<in> m" using M3 m meets_wd assms by blast
        with iu have "(l,j) \<in> b" using cmfi by auto
        moreover from li have "l \<in> (BEGIN i)" using BEGIN_def by auto
        ultimately show ?thesis using intv1  before_def NEST_BEGIN assms by blast
        next
        assume iu:"(j,i) \<in> d" 
        obtain l where li:"(l,i) \<in> m" using M3 m meets_wd assms by blast
        with iu have "(l,j) \<in> b" using cmdi by auto
        moreover from li have "l \<in> (BEGIN i)" using BEGIN_def by auto
        ultimately show ?thesis using intv1 before_def NEST_BEGIN assms by blast
        
     qed
qed

lemma BEGIN_END_before:
fixes i j
assumes "\<I> i" and "\<I> j"
shows  "BEGIN i \<lless> END j = ((i,j) \<in> e \<union> b \<union> m \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>) "
proof 
     assume a3:"BEGIN i \<lless> END j"
     then obtain p q where pa:"p \<in> BEGIN i" and qc:"q \<in> END j" and pq:"(p,q) \<in> b" unfolding before_def by auto
     then obtain r where "p\<parallel>r" and "r\<parallel>q" using b by auto
     then have pr:"(p,r) \<in> m" and rq:"(r,q) \<in> m" using m by auto
     from pa  have pi:"(p,i) \<in> ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
     moreover with pr have "(r,p) \<in> m^-1" by simp
     ultimately have "(r,i) \<in> d \<union> f \<union> ov^-1 \<union> e \<union> f^-1 \<union> m^-1 \<union> b^-1 \<union> s \<union> s^-1" using cmiov cmis cmim cmifi cmidi e cmisi
     by ( simp_all,elim disjE, auto simp:e)
     
     then have ir:"(i,r) \<in> d^-1 \<union> f^-1 \<union> ov \<union> e \<union> f \<union> m \<union> b \<union> s^-1 \<union> s" 
     by (metis (mono_tags, lifting) converseD converse_Un converse_converse eei)

     from qc  have "(q,j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
     with rq have rj:"(r,j) \<in> m \<union> ov \<union> s \<union> d \<union> b \<union> f^-1 \<union> f \<union> e" using cm_alpha1ialpha4mi by blast

     with ir show  c1:"(i,j) \<in> e \<union> b \<union> m \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>"
     using difimov by blast
     next
     assume a4:"(i, j) \<in> e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>"
     then show "BEGIN i \<lless> END j"
     proof  ( simp_all,elim disjE, simp_all)
           assume "(i,j) \<in> e" 
           obtain l k where l:"l\<parallel>i" and "i\<parallel>k" using M3 meets_wd assms  by blast
           with \<open>(i,j) \<in> e\<close> have k:"j\<parallel>k" by (simp add: e)
           from l k have "(l,i) \<in> m" and "(k,j) \<in> m^-1" using m by auto
           then  have "l \<in> BEGIN i" and "k \<in> END j" using BEGIN_def END_def by auto 
           moreover from l \<open>i\<parallel>k\<close> have "(l,k) \<in> b" using b by auto
           ultimately show ?thesis using before_def assms NEST_BEGIN NEST_END  by blast
          next
           assume "(i,j) \<in> b"
           then show ?thesis using before_def assms NEST_BEGIN NEST_END intv1[of i] intv2[of j] by auto
          next
            assume "(i,j) \<in> m"
            obtain l where "l\<parallel>i" using M3 assms by blast
            then have "l\<in>BEGIN i" using m BEGIN_def by auto
            moreover from \<open>(i,j)\<in>m\<close> \<open>l\<parallel>i\<close> have "(l,j) \<in> b" using b m by blast
            ultimately show ?thesis using intv2[of j] assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(i,j) \<in> ov"
           then obtain l k where li:"l\<parallel>i" and lk:"l\<parallel>k" and ku:"k\<parallel>j" using ov by blast
           from li have "l \<in> BEGIN i" using m BEGIN_def by auto
           moreover from lk ku have "(l,j) \<in> b" using b by auto
           ultimately show ?thesis using intv2[of j] assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(j,i) \<in> ov"
           then obtain l k v where uv:"j\<parallel>v" and lk:"l\<parallel>k" and kv:"k\<parallel>v" and li:"l\<parallel>i" using ov by blast
           from li have "l \<in> BEGIN i" using m BEGIN_def by auto
           moreover from uv have "v \<in> END j" using m END_def by auto
           moreover from lk kv have "(l,v) \<in> b" using b by auto
           ultimately show ?thesis using  assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(i,j) \<in> s"
           then obtain v v' where iv:"i\<parallel>v" and vvp:"v\<parallel>v'" and "j\<parallel>v'" using s by blast
           then have "v' \<in> END j" using END_def m by auto
           moreover from iv vvp have "(i,v') \<in> b" using b by auto
           ultimately show ?thesis using intv1[of i]  assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(j,i) \<in> s"
           then obtain l v where li:"l\<parallel>i" and lu:"l\<parallel>j" and "j\<parallel>v" using s by blast
           then have "v \<in> END j" using m END_def by auto
           moreover from li have "l \<in> BEGIN i" using m BEGIN_def by auto
           moreover from lu \<open>j\<parallel>v\<close> have "(l,v) \<in> b" using b by auto
           ultimately show ?thesis using  assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(i,j) : f"
           then obtain l v where li:"l\<parallel>i" and iv:"i\<parallel>v" and "j\<parallel>v" using f by blast
           then have "v \<in> END j" using m END_def by auto
           moreover from li have "l \<in> BEGIN i" using m BEGIN_def by auto
           moreover from iv li have "(l,v) \<in> b" using b by auto
           ultimately show ?thesis using assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(j,i) \<in> f"
           then obtain l v where li:"l\<parallel>i" and iv:"i\<parallel>v" and "j\<parallel>v" using f by blast
           then have "v \<in> END j" using m END_def by auto
           moreover from li have "l \<in> BEGIN i" using m BEGIN_def by auto
           moreover from iv li have "(l,v) \<in> b" using b by auto
           ultimately show ?thesis using  assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(i,j) : d"
           then obtain k v where ik:"i\<parallel>k" and kv:"k\<parallel>v" and "j\<parallel>v" using d by blast
           then have "v \<in> END j" using END_def m by auto
           moreover from ik kv have "(i,v) \<in> b" using b by auto
           ultimately show ?thesis using intv1[of i]  assms NEST_BEGIN NEST_END before_def by blast
          next
           assume "(j,i) \<in> d"
           then obtain l k where "l\<parallel>i" and lk:"l\<parallel>k" and ku:"k\<parallel>j" using d by blast
           then have "l \<in> BEGIN i" using BEGIN_def m by auto
           moreover from lk ku have "(l,j) \<in> b" using b by auto
           ultimately show ?thesis using intv2[of j] assms NEST_BEGIN NEST_END before_def by blast
       qed           
qed

lemma END_BEGIN_before:
fixes i j
assumes "\<I> i" and "\<I> j"
shows  "END i \<lless> BEGIN j =  ((i,j) \<in> b) "
proof 
     assume a3:"END i \<lless> BEGIN j"
     from a3 obtain p q where pa:"p \<in> END i" and qc:"q \<in> BEGIN j" and pq:"(p,q) \<in> b" unfolding before_def by auto
     then obtain r where "p\<parallel>r" and "r\<parallel>q" using b by auto
     then have pr:"(p,r) \<in> m" and rq:"(r,q) \<in> m" using m by auto
     from pa  have pi:"(p,i) \<in>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
     moreover with pr have "(r,p) \<in> m^-1" by simp
     ultimately have "(r,i) \<in> m^-1 \<union> b^-1" using e cmiovi cmisi cmidi cmif cmifi cmimi 
     by ( simp_all,elim disjE, auto simp:e)
     
     then have ir:"(i,r) \<in> m \<union> b" by simp
     
     from qc  have "(q,j) \<in>  ov \<union> s \<union> m \<union> f\<inverse> \<union> d\<inverse> \<union> e \<union> s\<inverse>" unfolding BEGIN_def by auto
     with rq have rj:"(r,j) \<in> b \<union> m " using cmov cms cmm cmfi cmdi e cmsi
     by (simp_all, elim disjE, auto simp:e)
     
     with ir show "(i,j) \<in> b" using cmb cmm cbm cbb by auto

   next
     assume "(i,j) \<in> b" thus "END i \<lless> BEGIN j" using intv1[of j] intv2[of i] assms before_def NEST_END NEST_BEGIN by auto
qed

lemma END_END_before:
fixes i j
assumes "\<I> i" and "\<I> j"
shows "END i \<lless> END j = ((i,j) \<in> b \<union> m \<union> ov \<union> s \<union> d) "
proof 
     assume a3:"END i \<lless> END j"
     from a3 obtain p q where pa:"p \<in> END i" and qc:"q \<in> END j" and pq:"(p,q) \<in> b" unfolding before_def by auto
     then obtain r where "p\<parallel>r" and "r\<parallel>q" using b by auto
     then have pr:"(p,r) \<in> m" and rq:"(r,q) \<in> m" using m by auto
     from pa  have pi:"(p,i) \<in>  e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
     moreover with pr have "(r,p) \<in> m^-1" by simp
     ultimately have "(r,i) \<in> m^-1 \<union> b^-1" using e cmiovi cmisi cmidi cmif cmifi cmimi 
     by ( simp_all,elim disjE, auto simp:e)
     
     then have ir:"(i,r) \<in> m \<union> b" by simp
     
     from qc  have "(q,j) \<in> e \<union> ov\<inverse> \<union> s\<inverse> \<union> d\<inverse> \<union> f \<union> f\<inverse> \<union> m\<inverse>" unfolding END_def by auto
     with rq have rj:"(r,j) \<in> m \<union> ov \<union> s \<union> d \<union> b \<union> f^-1 \<union> e \<union> f " using e cmovi cmsi cmdi cmf cmfi cmmi
     by (simp_all, elim disjE, auto simp:e)
     
     with ir show "(i,j) \<in> b \<union> m \<union> ov \<union> s \<union> d" using cmm cmov cms cmd cmb cmfi e cmf cbm cbov cbs cbd cbb cbfi cbf
     by (simp_all, elim disjE, auto simp:e)
    next
     assume "(i, j) \<in> b \<union> m \<union> ov \<union> s \<union> d"
     then show "END i \<lless> END j"
     proof  ( simp_all,elim disjE, simp_all)
        assume "(i,j) \<in> b" thus ?thesis using intv2[of i] intv2[of j] assms NEST_END before_def by blast
       next
        assume "(i,j) \<in> m" 
        obtain v where "j\<parallel>v" using M3 assms by blast
        with \<open>(i,j) \<in> m\<close> have "(i,v) \<in>b" using b m by blast
        moreover from \<open>j\<parallel>v\<close> have "v \<in> END j" using m END_def by auto
        ultimately show ?thesis using intv2[of i] assms NEST_END before_def by blast
       next
        assume "(i,j) : ov"
        then obtain v v' where iv:"i\<parallel>v" and vvp:"v\<parallel>v'" and "j\<parallel>v'" using ov by blast
        then have "v' \<in> END j" using m END_def by auto
        moreover from iv vvp have "(i,v') \<in> b" using b by auto
        ultimately show ?thesis using intv2[of i] assms NEST_END before_def by blast
       next
        assume "(i,j) \<in> s"
        then obtain v v' where iv:"i\<parallel>v" and vvp:"v\<parallel>v'" and "j\<parallel>v'" using s by blast
        then have "v' \<in> END j" using m END_def by auto
        moreover from iv vvp have "(i,v') \<in> b" using b by auto
        ultimately show ?thesis using intv2[of i] assms NEST_END before_def by blast
       next
        assume "(i,j) \<in> d"
        then obtain v v' where iv:"i\<parallel>v" and vvp:"v\<parallel>v'" and "j\<parallel>v'" using d by blast
        then have "v' \<in> END j" using m END_def by auto
        moreover from iv vvp have "(i,v') \<in> b" using b by auto
        ultimately show ?thesis using intv2[of i] assms NEST_END before_def by blast
       qed 
qed

lemma overlaps:
assumes "\<I> i" and "\<I> j"
shows "(i,j) \<in> ov = ((BEGIN i \<lless> BEGIN j) \<and> (BEGIN j \<lless> END i) \<and> (END i \<lless> END j))"
proof 

    assume a:"(i,j) \<in> ov"
    then obtain n t q  u v where nt:"n\<parallel>t" and tj:"t\<parallel>j" and tq:"t\<parallel>q" and qu:"q\<parallel>u" and  iu:"i\<parallel>u" and uv:"u\<parallel>v" and jv:"j\<parallel>v" and "n\<parallel>i" using ov by blast
    then have ni:"(n,i) \<in> m"  using  m  by blast
    then have  n:"n \<in> BEGIN i" unfolding BEGIN_def by auto
    from nt tj have nj:"(n,j) \<in> b" using b by auto
    have  "j \<in> BEGIN j" using assms(2) by (simp add: intv1)
    with assms n nj  have c1:"BEGIN i \<lless> BEGIN j" unfolding before_def using NEST_BEGIN by blast
  
    from tj have a1:"(t,j) \<in> m" and a2:"t \<in> BEGIN j" using m BEGIN_def by auto
    from iu have "(u,i) \<in> m^-1" and "u \<in> END i" using m END_def by auto
    with assms  tq qu a2 have c2:"BEGIN j \<lless> END i"  unfolding before_def using b  NEST_BEGIN NEST_END by blast

    have "i \<in> END i" by (simp add: assms  intv2) 
    moreover with jv  have "v \<in> END j" using m END_def by auto
    moreover with iu uv have "(i,v) \<in> b" using b by auto
    ultimately have c3:"END i \<lless> END j" using assms NEST_END before_def by blast

    show "((BEGIN i \<lless> BEGIN j) \<and> (BEGIN j \<lless> END i) \<and> (END i \<lless> END j))" using c1 c2 c3 by simp     
  next
    assume a0:"((BEGIN i \<lless> BEGIN j) \<and> (BEGIN j \<lless> END i) \<and> (END i \<lless> END j))"
    then have "(i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> \<and> (i,j) \<in> e \<union> b^-1 \<union> m^-1 \<union> ov^-1 \<union> ov \<union> s^-1 \<union> s \<union> f^-1 \<union> f \<union> d^-1 \<union> d
                                                                                                              \<and> (i,j) \<in> b \<union> m \<union> ov \<union> s \<union> d"
    using BEGIN_before BEGIN_END_before END_END_before assms 
    by (metis (no_types, lifting) converseD converse_Un converse_converse eei)
    then have "(i,j) \<in>  (b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>) \<inter> (e \<union> b^-1 \<union> m^-1 \<union> ov^-1 \<union> ov \<union> s^-1 \<union> s \<union> f^-1 \<union> f \<union> d^-1 \<union> d) \<inter> (b \<union> m \<union> ov \<union> s \<union> d)" 
    by (auto)
    then show "(i,j) \<in> ov"
    using inter_ov by blast

qed

subsection \<open>Ordering of nests\<close>

class  strict_order =
fixes ls::"'a nest \<Rightarrow> 'a nest \<Rightarrow> bool"
assumes 
  irrefl:"\<not> ls a a" and
  trans:"ls a c \<Longrightarrow> ls c g \<Longrightarrow> ls a g" and 
  asym:"ls a c \<Longrightarrow> \<not> ls c a"  

class total_strict_order = strict_order +
assumes trichotomy: "a = c \<Longrightarrow> (\<not> (ls a  c) \<and> \<not> (ls c  a))"

interpretation nest:total_strict_order "(\<lless>) "
proof
{ fix a::"'a nest"
show "\<not> a \<lless> a"
by (simp add: before_irrefl) } note  irrefl_nest = this

{fix a c::"'a nest"
assume  "a = c"
show "\<not> a \<lless> c \<and> \<not> c \<lless> a" 
by (simp add: \<open>a = c\<close> irrefl_nest)} note trichotomy_nest = this

{fix a c g::"'a nest"
assume a:"a \<lless> c" and c:" c \<lless> g"
show " a \<lless> g" 
proof -
   from a c have na:"NEST a"  and nc:"NEST c" and ng:"NEST g" unfolding before_def by auto
   from na obtain i where  i:"a = BEGIN i \<or> a = END i" and wdi:"\<I> i" unfolding NEST_def by auto
   from nc obtain j where  j:"c = BEGIN j \<or> c = END j" and wdj:"\<I> j" unfolding NEST_def by auto
   from ng obtain u where  u:"g = BEGIN u \<or> g = END u" and wdu:"\<I> u" unfolding NEST_def by auto
   from i j u show ?thesis
   proof (elim disjE, auto)
     assume abi:"a = BEGIN i" and  cbj:"c = BEGIN j" and  gbu:"g = BEGIN u"
     from abi cbj a wdi wdj have "(i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> " using BEGIN_before by auto
     moreover from cbj gbu c wdj wdu have "(j,u) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>" using BEGIN_before by auto

     ultimately have c1:"(i,u) \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
     using cbeta2_beta2 by blast
      
     then have "a \<lless> g" by (simp add: BEGIN_before abi gbu wdi wdu)
    
     thus "BEGIN i \<lless> BEGIN u" using abi gbu by auto
    next
     assume  abi:"a = BEGIN i" and  cbj:"c = BEGIN j" and  geu:"g = END u" 
     from abi cbj a wdi wdj have "(i,j) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse> " using BEGIN_before by auto
     moreover from cbj geu c wdj wdu have "(j,u) :  e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>" using BEGIN_END_before by auto
     ultimately have "(i,u) \<in> e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>"
     using cbeta2_gammabm by blast
          
     then have "a \<lless> g" 
     by (simp add: BEGIN_END_before abi geu wdi wdj wdu)
       
     thus "BEGIN i \<lless> END u" using abi geu by auto
    next
     assume abi:"a = BEGIN i" and  cej:"c = END j" and  gbu:"g = BEGIN u"
     from abi cej a wdi wdj  have ij:"(i,j) :  e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>" using BEGIN_END_before by auto
     from cej gbu c wdj wdu  have "(j,u) \<in> b " using END_BEGIN_before by auto
     with ij have "(i,u) \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1" 
     using ebmovovissifsiddib by ( auto)

     thus "BEGIN i \<lless> BEGIN u"
     by (simp add: BEGIN_before abi gbu wdi wdu)
    next
     assume abi:"a = BEGIN i" and  cej:"c = END j" and  geu:"g = END u"
     with a  have "(i,j) \<in>  e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>"
     using BEGIN_END_before wdi wdj by auto
     moreover from cej geu c wdj wdu  have "(j,u) \<in> b \<union> m \<union> ov \<union> s \<union> d"
     using END_END_before by auto
     ultimately have "(i,u) \<in> b \<union> m \<union> ov \<union> s \<union> d \<union> f^-1 \<union> d^-1 \<union> ov^-1 \<union> s\<inverse> \<union> f \<union> e"
     using ebmovovissiffiddibmovsd by blast
                  
     thus "BEGIN i \<lless> END u" using BEGIN_END_before wdi wdu  by auto
    next
     assume aei:"a = END i" and cbj:"c = BEGIN j" and gbu:"g = BEGIN u"
     from a  aei cbj wdi wdj have "(i,j) \<in> b"
     using END_BEGIN_before by auto
     moreover from c  cbj gbu wdj wdu have "(j,u) \<in> b \<union> m \<union> ov \<union> f\<inverse> \<union> d\<inverse>" 
     using BEGIN_before by auto 
     ultimately have "(i,u) : b" using cbb cbm cbov cbfi cbdi 
     by (simp_all, elim disjE, auto)
     thus "END i \<lless> BEGIN u" using END_BEGIN_before wdi wdu  by auto
    next
     assume  aei:"a = END i" and cbj:"c = BEGIN j" and  geu:"g = END u"
     from a  aei cbj wdi wdj have "(i,j) \<in> b"
     using END_BEGIN_before by auto
     moreover from c  cbj geu wdj wdu have "(j,u) \<in> e \<union> b \<union> m \<union> ov \<union> ov\<inverse> \<union> s \<union> s\<inverse> \<union> f \<union> f\<inverse> \<union> d \<union> d\<inverse>" 
     using BEGIN_END_before by auto 
     ultimately have "(i,u) \<in> b \<union> m \<union> ov \<union> s \<union> d"
     using bebmovovissiffiddi by blast
     thus "END i \<lless> END u" using END_END_before wdi wdu by auto
    next
     assume aei:"a = END i" and cej:"c = END j" and  gbu:"g = BEGIN u" 
     from aei cej wdi wdj have "(i,j) \<in> b \<union> m \<union> ov \<union> s \<union> d" using END_END_before a by auto
     moreover from cej gbu c wdj wdu have "(j,u) \<in> b" using END_BEGIN_before by auto
     ultimately have "(i,u) \<in> b"
     using cbb cmb covb csb cdb
     by (simp_all, elim disjE, auto)
     thus "END i \<lless> BEGIN u" using END_BEGIN_before wdi wdu  by auto
    next
     assume aei:"a = END i" and cej:"c = END j" and geu:"g = END u"
     from aei cej wdi wdj  have "(i,j) \<in> b \<union> m \<union> ov \<union> s \<union> d" using  END_END_before a by auto
     moreover from cej geu c wdj wdu have "(j,u) \<in>  b \<union> m \<union> ov \<union> s \<union> d" using END_END_before by auto
     ultimately have "(i,u) \<in> b \<union> m \<union> ov \<union> s \<union> d" 
     using calpha1_alpha1 by auto
     thus "END i \<lless> END u" using END_END_before wdi wdu by auto
   qed
qed} note trans_nest = this    

{ fix a c::"'a nest"
  assume a:"a \<lless> c"
  show "\<not> c \<lless> a"
  apply (rule ccontr, auto)
  using a  irrefl_nest trans_nest by blast}
qed  
         
end

