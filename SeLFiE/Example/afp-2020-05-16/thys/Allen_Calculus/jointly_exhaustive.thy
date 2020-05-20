(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)



theory jointly_exhaustive

imports
  allen

begin

section \<open>JE property\<close>
text \<open>The 13 time interval relations are jointly exhaustive. For any two intervals $x$ and $y$, we can find a basic relation $r$ such that $(x,y) \in r$.\<close>
 
lemma (in arelations) jointly_exhaustive:
assumes  "\<I> p" "\<I> q"
shows "(p::'a,q::'a) \<in> b \<or> (p,q) \<in> m \<or> (p,q) \<in> ov \<or> (p,q) \<in> s \<or> (p,q) \<in> d \<or> (p,q) \<in> f^-1 \<or> (p,q) \<in> e \<or> 
                                    (p,q) \<in> f \<or> (p,q) \<in> s^-1 \<or> (p,q) \<in> d^-1 \<or> (p,q) \<in> ov^-1 \<or> (p,q) \<in> m^-1 \<or> (p,q) \<in> b^-1 " (is ?R)
proof -
  obtain k k' u u'::'a where kp:"k\<parallel>p" and kpq:"k'\<parallel>q" and pu:"p\<parallel>u" and qup:"q\<parallel>u'" using M3 meets_wd assms(1,2) by fastforce
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus ?thesis
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have kq:?A by simp
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'::'a. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp
           with kp kq qup have "p = q" using M4 by auto
           thus ?thesis using  e  by auto}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have "?B" by simp
           with kq kp qup show ?thesis using  s by blast}
          next
          {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
           then obtain t' where "q\<parallel>t'" and "t'\<parallel>u" by blast
           with kq kp pu show ?thesis using  s by blast }
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with kp qup kt tq show ?thesis using f  by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C"  then have ?B by simp
           then obtain t' where ptp:"p\<parallel>t'" and tpup:"t'\<parallel>u'" by auto
           from pu tq  have "p\<parallel>q \<oplus> ((\<exists>t''. p\<parallel>t'' \<and> t''\<parallel>q) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using  m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using  b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
                then obtain g where "t\<parallel>g" and "g\<parallel>u" by auto
                moreover with pu ptp have "g\<parallel>t'" using M1 by blast
                ultimately  show ?thesis using  ov kt tq kp ptp tpup qup   by blast}
           qed}
         next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
           then obtain t' where "q\<parallel>t'" and "t'\<parallel>u" by auto
           with kp  kt tq pu show ?thesis using d  by blast}
         qed}
      next
      { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
        then obtain t where kpt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
        from  pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qup kpt tp kpq show ?thesis using  f by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
           with qup kpt tp kpq show ?thesis using  d by blast}
          next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain t' where qt':"q\<parallel>t'" and tpc:"t'\<parallel>u" by auto
           from qup tp have "q\<parallel>p \<oplus> ((\<exists>t''. q\<parallel>t'' \<and> t''\<parallel>p) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u'))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using  m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using  b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain g where tg:"t\<parallel>g" and "g\<parallel>u'" by auto
                with qup qt' have "g\<parallel>t'" using M1 by blast
                with qt' tpc pu kpq kpt tp tg show ?thesis using  ov by blast}
          qed}
     qed}
 qed
qed

lemma (in arelations) JE:
assumes "\<I> p" "\<I> q" 
shows "(p::'a,q::'a) \<in> b \<union> m  \<union> ov  \<union> s \<union> d \<union> f^-1 \<union> e \<union> f  \<union> s^-1  \<union> d^-1 \<union> ov^-1 \<union> m^-1  \<union> b^-1 "
using jointly_exhaustive UnCI assms(1,2) by blast


end
