(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)



theory axioms

imports
    Main  xor_cal

begin


section \<open>Axioms\<close>

text\<open>We formalize Allen's definition of theory of time in term of intervals (Allen, 1983). 
Two relations, namely meets and equality, are defined between intervals. Two interval meets if they  are adjacent 
A set of 5 axioms ((M1) $\sim$ (M5)) are then defined based on relation meets.\<close>

text\<open>We define a class interval whose assumptions are (i) properties of relations meets  and, (ii) axioms (M1) $\sim$ (M5).\<close>

class interval =
 fixes
  meets::"'a \<Rightarrow> 'a \<Rightarrow> bool"  (infixl "\<parallel>" 60) and
  \<I>::"'a \<Rightarrow> bool"
 assumes
  meets_atrans:"\<lbrakk>(p\<parallel>q);(q\<parallel>r)\<rbrakk> \<Longrightarrow> \<not>(p\<parallel>r)" and
  meets_irrefl:"\<I> p \<Longrightarrow> \<not>(p\<parallel>p)" and
  meets_asym:"(p\<parallel>q) \<Longrightarrow> \<not>(q\<parallel>p)" and
  meets_wd:"p\<parallel>q \<Longrightarrow> \<I> p \<and> \<I> q" and
(**** Time axioms ******)
  M1:"\<lbrakk>(p\<parallel>q); (p\<parallel>s); (r\<parallel>q)\<rbrakk> \<Longrightarrow> (r\<parallel>s)" and
  M2:"\<lbrakk>(p\<parallel>q) ; (r\<parallel>s)\<rbrakk> \<Longrightarrow> p\<parallel>s \<oplus> ((\<exists>t. (p\<parallel>t)\<and>(t\<parallel>s)) \<oplus> (\<exists>t. (r\<parallel>t)\<and>(t\<parallel>q)))" and
  M3:"\<I> p \<Longrightarrow> (\<exists>q r. q\<parallel>p \<and> p\<parallel>r)" and
  M4:"\<lbrakk>p\<parallel>q ; q\<parallel>s ; p\<parallel>r ; r\<parallel>s\<rbrakk> \<Longrightarrow> q = r"  and
  M5exist:"p\<parallel>q \<Longrightarrow> (\<exists>r s t. r\<parallel>p \<and> p\<parallel>q \<and> q\<parallel>s \<and> r\<parallel>t \<and> t\<parallel>s)" 
(**********)

lemma  (in interval) trans2:"\<lbrakk>p\<parallel>t; t\<parallel>r; r\<parallel>q\<rbrakk> \<Longrightarrow> \<not>p\<parallel>q"
  using M1 meets_asym by blast

lemma (in interval) nontrans1: "u\<parallel>r \<Longrightarrow> \<not> (\<exists>t. u\<parallel>t \<and> t\<parallel>r)"
  using meets_atrans by blast
 
lemma (in interval) nontrans2:"u\<parallel>r \<Longrightarrow> \<not> (\<exists>t. r\<parallel>t \<and> t\<parallel>u)"
  using M1 M5exist trans2 by blast

lemma (in interval) nonmeets1:"\<not> (u\<parallel>r \<and> r\<parallel>u)" 
  using meets_asym by blast

lemma (in interval)  nonmeets2: "\<lbrakk>\<I> u ; \<I> r \<rbrakk> \<Longrightarrow> \<not> (u\<parallel>r \<and> u = r)" 
  using meets_irrefl by blast

lemma (in interval) nonmeets3: "\<not> (u\<parallel>r \<and> (\<exists>p. u\<parallel>p \<and> p\<parallel>r))" 
  using nontrans1 by blast

lemma (in interval) nonmeets4: "\<not>(u\<parallel>r \<and> (\<exists>p. r\<parallel>p \<and> p\<parallel>u))" 
  using nontrans2 by blast

lemma (in interval) elimmeets: "(p \<parallel> s \<and> (\<exists>t. p \<parallel> t \<and> t \<parallel> s) \<and> (\<exists>t. r \<parallel> t \<and> t \<parallel> q)) = False"
  using meets_atrans by blast 

lemma (in interval) M5exist_var:
assumes "x\<parallel>y" "y\<parallel>z" "z\<parallel>w"
shows "\<exists>t. x\<parallel>t \<and> t\<parallel>w"
proof -
  from assms(1,3) have a:"x\<parallel>w \<oplus> (\<exists>t. x\<parallel>t \<and> t\<parallel>w) \<oplus> (\<exists>t. z\<parallel>t \<and> t\<parallel>y)" using M2[of x y z w] by auto
  from assms have b1:"\<not>x\<parallel>w" using trans2 by blast
  from assms(2) have "\<not> (\<exists>t. z\<parallel>t \<and> t\<parallel>y)" by (simp add: nontrans2)
  with b1 a have " (\<exists>t. x\<parallel>t \<and> t\<parallel>w)" by simp
  thus ?thesis by simp
qed

lemma (in interval) M5exist_var2:
assumes "p\<parallel>q"
shows "\<exists>r1 r2 r3 s t. r1\<parallel>r2 \<and> r2\<parallel>r3 \<and> r3\<parallel>p \<and> p\<parallel>q \<and> q\<parallel>s \<and> r1\<parallel>t \<and> t\<parallel>s"
proof -
  from assms obtain r3 k1 s  where r3p:"r3\<parallel>p" and  qs:"q\<parallel>s"  and  r3k1:"r3 \<parallel>k1"  and  k1s:"k1\<parallel>s" using M5exist by blast 
  from r3p obtain r2 where r2r3:"r2\<parallel>r3" using M3[of r3] meets_wd by auto
  from r2r3 obtain r1 where r1r2:"r1\<parallel>r2" using M3[of r2] meets_wd by auto
  with  assms  r2r3 r3p qs obtain t where r1t1:"r1\<parallel>t" and t1q:"t\<parallel>s" using M5exist_var by blast
  with assms r1r2 r2r3 r3p qs show ?thesis by blast
qed
  
lemma (in interval) M5exist_var3:
assumes "k\<parallel>l" and "l\<parallel>q" and "q\<parallel>t" and "t\<parallel>r" 
shows  "\<exists>lqt. k\<parallel>lqt \<and> lqt\<parallel>r"
proof -
  from assms(1-3) obtain lq where "k\<parallel>lq" and "lq\<parallel>t" 
  using M5exist_var by blast 
  with assms(4) obtain lqt where "k\<parallel>lqt" and "lqt\<parallel>r" 
  using M5exist_var by blast
  thus ?thesis by auto
qed


end
