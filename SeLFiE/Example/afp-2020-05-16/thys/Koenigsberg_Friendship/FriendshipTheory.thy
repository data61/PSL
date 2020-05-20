(*
Title: FriendshipTheory.thy
Author:Wenda Li
*)

theory FriendshipTheory 
  imports MoreGraph  "HOL-Number_Theory.Number_Theory"
begin

(*Proofs in this section are the common steps for both combinatorial and algebraic proofs for the
Friendship Theorem*)
section\<open>Common steps\<close>

definition (in valid_unSimpGraph) non_adj :: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "non_adj v v' \<equiv> v\<in>V \<and> v'\<in>V \<and> v\<noteq>v' \<and> \<not>adjacent v v'" 

lemma (in valid_unSimpGraph) no_quad:
  assumes "\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
  shows "\<not> (\<exists>v1 v2 v3 v4. v2\<noteq>v4 \<and> v1\<noteq>v3 \<and> adjacent v1 v2 \<and> adjacent v2 v3 \<and> adjacent v3 v4 
      \<and> adjacent v4 v1)"
proof
  assume "\<exists>v1 v2 v3 v4. v2\<noteq>v4  \<and> v1\<noteq>v3 \<and> adjacent v1 v2 \<and> adjacent v2 v3 \<and> adjacent v3 v4 \<and> adjacent v4 v1"
  then obtain v1 v2 v3 v4 where 
    "v2\<noteq>v4" "v1\<noteq>v3" "adjacent v1 v2" "adjacent v2 v3" "adjacent v3 v4" "adjacent v4 v1"
    by auto
  hence "\<exists>!n. adjacent v1 n \<and> adjacent v3 n" using assms[of v1 v3] by auto
  thus False 
    by (metis \<open>adjacent v1 v2\<close> \<open>adjacent v2 v3\<close> \<open>adjacent v3 v4\<close> \<open>adjacent v4 v1\<close> \<open>v2 \<noteq> v4\<close> 
      adjacent_sym)
qed 

lemma even_card_set: 
  assumes "finite A" and "\<forall>x\<in>A. f x\<in>A \<and> f x\<noteq> x \<and> f (f x)=x"
  shows "even(card A)" using assms
proof (induct "card A"  arbitrary:A rule:less_induct)
  case less
  have "A={}\<Longrightarrow>?case" by auto
  moreover have "A\<noteq>{}\<Longrightarrow>?case" 
    proof -
      assume "A\<noteq>{}"
      then obtain x where "x\<in>A" by auto
      hence "f x\<in>A" and "f x\<noteq>x" by (metis less.prems(2))+
      obtain B where B:"B=A-{x,f x}" by auto
      hence "finite B" using \<open>finite A\<close> by auto
      moreover have "card B<card A" using B \<open>finite A\<close> 
        by (metis Diff_insert \<open>f x \<in> A\<close> \<open>x \<in> A\<close> card_Diff2_less)
      moreover have "\<forall>x\<in>B. f x \<in> B \<and> f x \<noteq> x \<and> f (f x) = x" 
        proof 
          fix y assume "y\<in>B"
          hence "y\<in>A" using B by auto
          hence "f y\<noteq>y" and "f (f y)=y" by (metis less.prems(2))+
          moreover have "f y\<in>B" 
            proof (rule ccontr)
              assume "f y\<notin>B"
              have "f y\<in>A" by (metis \<open>y \<in> A\<close> less.prems(2))
              hence "f y\<in>{x, f x}" by (metis B DiffI \<open>f y \<notin> B\<close>)
              moreover have "f y=x \<Longrightarrow> False" 
                by (metis B Diff_iff Diff_insert2 \<open>f (f y) = y\<close> \<open>y \<in> B\<close> singleton_iff)
              moreover have "f y= f x\<Longrightarrow> False" 
                by (metis B Diff_iff \<open>x \<in> A\<close> \<open>y \<in> B\<close> insertCI less.prems(2))
              ultimately show False by auto
            qed
          ultimately show "f y \<in> B \<and> f y \<noteq> y \<and> f (f y) = y"  by auto
        qed
      ultimately have "even (card B)" by (metis (full_types) less.hyps)
      moreover have "{x,f x}\<subseteq>A" using \<open>f x\<in>A\<close> \<open>x\<in>A\<close> by auto
      moreover have "card {x, f x} = 2" using \<open>f x\<noteq>x\<close> by auto
      ultimately show ?case using B \<open>finite A\<close> card_mono [of A "{x, f x}"] 
        by (simp add: card_Diff_subset)
    qed
  ultimately show ?case by metis
qed

lemma (in valid_unSimpGraph) even_degree:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E"
  shows "\<forall>v\<in>V. even(degree v G)"
proof 
  fix v assume "v\<in>V"
  obtain f where f:"f = (\<lambda>n. (SOME v'. n\<in>V \<longrightarrow>n\<noteq>v\<longrightarrow>adjacent n v' \<and> adjacent v v'))" by auto
  have "\<And>n.  n\<in>V \<longrightarrow> n\<noteq>v \<longrightarrow> (\<exists>v'. adjacent n v' \<and> adjacent v v')" 
    proof (rule,rule)
      fix n assume  "n \<in> V" "n \<noteq> v" 
      hence "\<exists>!v'. adjacent n v' \<and> adjacent v v'" 
        using friend_assm[of n v] \<open>v\<in>V\<close>  unfolding non_adj_def by auto
      thus "\<exists>v'. adjacent n v' \<and> adjacent v v'"  by auto
    qed
  hence f_ex:"\<And>n.  (\<exists>v'. n\<in>V \<longrightarrow> n\<noteq>v \<longrightarrow>  adjacent n v' \<and> adjacent v v')" by auto
  have "\<forall>x\<in>{n. adjacent v n}. f x\<in>{n. adjacent v n} \<and> f x\<noteq> x \<and> f (f x)=x" 
    proof 
      fix x assume "x \<in> {n. adjacent v n}"
      hence "adjacent v x" by auto
      have "f x\<in>{n. adjacent v n}" 
        using someI_ex[OF f_ex,of x] 
        by (metis \<open>adjacent v x\<close> adjacent_V(2) adjacent_no_loop f mem_Collect_eq)
      moreover have "f x\<noteq>x" 
        using someI_ex[OF f_ex,of x] 
        by (metis \<open>adjacent v x\<close> adjacent_V(2) adjacent_no_loop f)
      moreover have "f (f x)=x" 
        proof (rule ccontr)
          assume "f (f x)\<noteq>x"
          have "adjacent (f x) (f (f x))"  
            using someI_ex[OF f_ex,of "f x"] 
            by (metis (full_types) adjacent_V(2) adjacent_no_loop calculation(1) f mem_Collect_eq) 
          moreover have "adjacent (f (f x)) v"
            using someI_ex[OF f_ex,of "f x"] by (metis adjacent_V(1) adjacent_sym calculation f)
          moreover have "adjacent x (f x)" 
            using someI_ex[OF f_ex,of x] by (metis \<open>adjacent v x\<close> adjacent_V(2) adjacent_no_loop f)
          moreover have "v\<noteq>f x" 
            by (metis \<open>f x \<in> {n. adjacent v n}\<close> adjacent_no_loop mem_Collect_eq)
          ultimately show False 
            using no_quad[OF friend_assm] using \<open>adjacent v x\<close> \<open>f (f x)\<noteq>x\<close> 
            by metis
        qed 
      ultimately show "f x \<in> {n. adjacent v n} \<and> f x \<noteq> x \<and> f (f x) = x" by auto
    qed
  moreover have "finite {n. adjacent v n}" by (metis adjacent_finite assms(2))
  ultimately have "even (card {n. adjacent v n})" 
    using even_card_set[of "{n. adjacent v n}" f] by auto
  thus "even(degree v G)" by (metis assms(2) degree_adjacent)
qed

lemma (in valid_unSimpGraph) degree_two_windmill:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite E" and "card V\<ge>2"
  shows "(\<exists>v\<in>V. degree v G = 2) \<longleftrightarrow>(\<exists>v. \<forall>n\<in>V. n\<noteq>v \<longrightarrow> adjacent v n)"
proof 
  assume "\<exists>v\<in>V. degree v G = 2 "
  then obtain v where "degree v G=2" by auto
  hence "card {n. adjacent v n}=2" using degree_adjacent[OF \<open>finite E\<close>,of v] by auto  
  then obtain v1 v2 where v1v2:"{n. adjacent v n}={v1,v2}" and "v1\<noteq>v2"
    proof -
      obtain v1 S where "{n. adjacent v n} = insert v1 S" and  "v1 \<notin> S" and "card S = 1"
        using \<open>card {n. adjacent v n}=2\<close> card_Suc_eq[of "{n. adjacent v n}" 1] by auto
      then obtain v2 where "S=insert v2 {}" 
        using card_Suc_eq[of S 0] by auto
      hence "{n. adjacent v n}={v1,v2}" and "v1\<noteq>v2" 
        using \<open>{n. adjacent v n} = insert v1 S\<close> \<open>v1 \<notin> S\<close> by auto
      thus ?thesis using that[of v1 v2] by auto
    qed
  have "adjacent v1 v2" 
    proof -
      obtain n where "adjacent v n" "adjacent v1 n" using friend_assm[of v v1] 
        by (metis (full_types) adjacent_V(2) adjacent_sym insertI1 mem_Collect_eq v1v2)
      hence "n\<in>{n. adjacent v n}" by auto
      moreover have "n\<noteq>v1" by (metis \<open>adjacent v1 n\<close> adjacent_no_loop)
      ultimately have "n=v2" using v1v2 by auto
      thus ?thesis by (metis \<open>adjacent v1 n\<close>)
    qed
  have v1v2_adj:"\<forall>x\<in>V. x\<in>{n. adjacent v1 n} \<union> {n. adjacent v2 n}"
    proof 
      fix x assume "x\<in>V"
      have "x=v \<Longrightarrow> x \<in> {n. adjacent v1 n} \<union> {n. adjacent v2 n}" 
        by (metis Un_iff adjacent_sym insertI1 mem_Collect_eq v1v2)
      moreover have "x\<noteq>v \<Longrightarrow> x \<in> {n. adjacent v1 n} \<union> {n. adjacent v2 n}" 
        proof -
          assume "x\<noteq>v"
          then obtain y where "adjacent v y" "adjacent x y"
            using friend_assm[of v x] 
            by (metis Collect_empty_eq \<open>x \<in> V\<close> adjacent_V(1) all_not_in_conv insertCI v1v2)
          hence "y=v1 \<or> y=v2" using v1v2 by auto
          thus "x \<in> {n. adjacent v1 n} \<union> {n. adjacent v2 n}" using \<open>adjacent x y\<close> 
            by (metis UnI1 UnI2 adjacent_sym mem_Collect_eq)
        qed
      ultimately show "x \<in> {n. adjacent v1 n} \<union> {n. adjacent v2 n}" by auto
    qed
  have "{n. adjacent v1 n}-{v2,v}={} \<Longrightarrow> \<exists>v. \<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n" 
    proof (rule exI[of _ v2],rule,rule) 
      fix n assume v1_adj:"{n. adjacent v1 n} - {v2, v} = {}" and "n \<in> V" and "n \<noteq> v2"
      have "n\<in>{n. adjacent v2 n}" 
        proof (cases "n=v") 
          case True
          show ?thesis by (metis True adjacent_sym insertI1 insert_commute mem_Collect_eq v1v2)
        next
          case False
          have "n\<notin>{n. adjacent v1 n}" by (metis DiffI False \<open>n \<noteq> v2\<close> empty_iff insert_iff v1_adj)
          thus ?thesis by (metis Un_iff \<open>n \<in> V\<close> v1v2_adj)
        qed
      thus "adjacent v2 n" by auto 
    qed
  moreover have "{n. adjacent v2 n}-{v1,v}={} \<Longrightarrow> \<exists>v. \<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n" 
    proof (rule exI[of _ v1],rule,rule) 
      fix n assume v2_adj:"{n. adjacent v2 n} - {v1, v} = {}" and "n \<in> V" and "n \<noteq> v1"
      have "n\<in>{n. adjacent v1 n}" 
        proof (cases "n=v") 
          case True
          show ?thesis by (metis True adjacent_sym insertI1 mem_Collect_eq v1v2)
        next
          case False
          have "n\<notin>{n. adjacent v2 n}" by (metis DiffI False \<open>n \<noteq> v1\<close> empty_iff insert_iff v2_adj)
          thus ?thesis by (metis Un_iff \<open>n \<in> V\<close> v1v2_adj)
        qed
      thus "adjacent v1 n" by auto 
    qed
  moreover have "{n. adjacent v1 n}-{v2,v}\<noteq>{} \<Longrightarrow> {n. adjacent v2 n}-{v1,v}\<noteq>{} \<Longrightarrow>False" 
    proof -
      assume "{n. adjacent v1 n} - {v2, v} \<noteq> {}"  "{n. adjacent v2 n} - {v1, v} \<noteq> {}"
      then obtain a b where a:"a\<in>{n. adjacent v1 n} - {v2, v}" 
          and b:"b\<in>{n. adjacent v2 n} - {v1, v}"
        by auto
      have "a=b \<Longrightarrow> False"
        proof -
          assume "a=b"
          have "adjacent v1 a" using a by auto
          moreover have "adjacent a v2" using b \<open>a=b\<close> adjacent_sym by auto
          moreover have "a\<noteq>v" by (metis DiffD2 \<open>a = b\<close> b doubleton_eq_iff insertI1)
          moreover have "adjacent v2 v" 
            by (metis (full_types) adjacent_sym inf_sup_aci(5) insertI1 insert_is_Un mem_Collect_eq 
              v1v2)
          moreover have "adjacent v v1" by (metis (full_types) insertI1 mem_Collect_eq v1v2)
          ultimately show False using no_quad[OF friend_assm] 
            using \<open>v1\<noteq>v2\<close> by auto
        qed
      moreover have "a\<noteq>b\<Longrightarrow>False"
        proof -
          assume "a\<noteq>b"
          moreover have "a\<in>V" using a by (metis DiffD1 adjacent_V(2) mem_Collect_eq)
          moreover have "b\<in>V" using b by (metis DiffD1 adjacent_V(2) mem_Collect_eq)
          ultimately obtain c where "adjacent a c" "adjacent b c"
            using friend_assm[of a b] by auto
          hence "c\<in>{n. adjacent v1 n} \<union> {n. adjacent v2 n}" 
            by (metis (full_types) adjacent_V(2) v1v2_adj)
          moreover have "c\<in>{n. adjacent v1 n} \<Longrightarrow> False" 
            proof -
              assume "c\<in>{n. adjacent v1 n}"
              hence "adjacent v1 c" by auto
              moreover have "adjacent c b" by (metis \<open>adjacent b c\<close> adjacent_sym)
              moreover have "adjacent b v2" 
                by (metis (full_types) Diff_iff adjacent_sym b mem_Collect_eq)
              moreover have "adjacent v2 v1" by (metis \<open>adjacent v1 v2\<close> adjacent_sym)
              moreover have "c\<noteq>v2" 
                proof (rule ccontr)
                  assume "\<not> c \<noteq> v2"
                  hence "c=v2" by auto
                  hence "adjacent v2 a" by (metis \<open>adjacent a c\<close> adjacent_sym)
                  moreover have "adjacent v2 v" 
                    by (metis adjacent_sym insert_iff mem_Collect_eq v1v2)
                  moreover have "adjacent v1 v" 
                    using adjacent_sym v1v2 by auto
                  moreover have "adjacent v1 a" by (metis (full_types) Diff_iff a mem_Collect_eq)
                  ultimately have "a=v" using friend_assm[of v1 v2] 
                    by (metis \<open>v1 \<noteq> v2\<close> adjacent_V(1)) 
                  thus False using a by auto
                qed
              moreover have "b\<noteq>v1" by (metis DiffD2 b insertI1)
              ultimately show False using no_quad[OF friend_assm] by auto
            qed
          moreover have "c\<in>{n. adjacent v2 n} \<Longrightarrow> False" 
            proof -
              assume "c\<in>{n. adjacent v2 n}"
              hence "adjacent c v2" by (metis adjacent_sym mem_Collect_eq)
              moreover have "adjacent a c" using \<open>adjacent a c\<close> .
              moreover have "adjacent v1 a" by (metis (full_types) Diff_iff a mem_Collect_eq) 
              moreover have "adjacent v2 v1" by (metis \<open>adjacent v1 v2\<close> adjacent_sym)
              moreover have "c\<noteq>v1" 
                proof (rule ccontr)
                  assume "\<not> c \<noteq> v1"
                  hence "c=v1" by auto
                  hence "adjacent v1 b" by (metis \<open>adjacent b c\<close> adjacent_sym)
                  moreover have "adjacent v2 v" 
                    by (metis adjacent_sym insert_iff mem_Collect_eq v1v2)
                  moreover have "adjacent v1 v" 
                    using adjacent_sym v1v2 by auto
                  moreover have "adjacent v2 b" by (metis Diff_iff b mem_Collect_eq)
                  ultimately have "b=v" using friend_assm[of v1 v2] 
                    by (metis \<open>v1 \<noteq> v2\<close> adjacent_V(1)) 
                  thus False using b by auto
                qed
              moreover have "a\<noteq>v2" by (metis DiffD2 a insertI1)
              ultimately show False using no_quad[OF friend_assm] by auto
            qed
          ultimately show False by auto
        qed
      ultimately show False by auto
    qed
  ultimately show "\<exists>v. \<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n" by auto
next
  assume "\<exists>v. \<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n"
  then obtain v where v:"\<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n" by auto
  obtain v1 where "v1\<in>V" "v1\<noteq>v" 
    proof (cases "v\<in>V") 
      case False
      have "V\<noteq>{}" using \<open>2\<le>card V\<close> by auto 
      then obtain v1 where "v1\<in>V" by auto
      thus ?thesis using False that[of v1] by auto
    next
      case True
      then obtain S where  "V = insert v S" "v \<notin> S"
        using  mk_disjoint_insert[OF True] by auto
      moreover have "finite V" using \<open>2\<le>card V\<close> 
        by (metis add_leE card_infinite not_one_le_zero numeral_Bit0 numeral_One)
      ultimately have "1\<le>card S" 
        using \<open>2\<le>card V\<close>  card.insert[of S v]  finite_insert[of v S] by auto
      hence "S\<noteq>{}" by auto
      then obtain v1 where "v1\<in>S" by auto
      hence "v1\<noteq>v" using \<open>v\<notin>S\<close> by auto
      thus thesis using that[of v1] \<open>v1\<in>S\<close> \<open>V=insert v S\<close> by auto
    qed
  hence "v\<in>V" using v by (metis adjacent_V(1)) 
  then obtain v2 where "adjacent v1 v2" "adjacent v v2" using friend_assm[of v v1] 
    by (metis \<open>v1 \<in> V\<close> \<open>v1 \<noteq> v\<close>)
  have "degree v1 G\<noteq>2 \<Longrightarrow> False" 
    proof -
      assume "degree v1 G\<noteq>2"
      hence "card {n. adjacent v1 n}\<noteq>2" by (metis assms(2) degree_adjacent)
      have "{v,v2} \<subseteq> {n. adjacent v1 n}" 
        by (metis \<open> adjacent v1 v2 \<close> \<open> v1 \<in> V \<close> \<open> v1 \<noteq> v \<close> adjacent_sym bot_least insert_subset 
          mem_Collect_eq v)
      moreover have "v\<noteq>v2" using \<open>adjacent v v2\<close> adjacent_no_loop by auto
      hence "card {v,v2} = 2" by auto 
      ultimately have "card {n. adjacent v1 n} \<ge>2" 
        using adjacent_finite[OF \<open>finite E\<close>, of v1] by (metis card_mono)
      hence "card {n. adjacent v1 n} \<ge>3" using \<open>card {n. adjacent v1 n}\<noteq>2\<close> by auto
      then obtain v3 where "v3\<in>{n. adjacent v1 n}" and "v3\<notin>{v,v2}"
        using \<open>{v,v2} \<subseteq> {n. adjacent v1 n}\<close> \<open>card {v, v2} = 2\<close>  
        by (metis \<open>card {n. adjacent v1 n} \<noteq> 2\<close> subsetI subset_antisym)
      hence "adjacent v1 v3" by auto
      moreover have "adjacent v3 v" using v 
        by (metis \<open>v3 \<notin> {v, v2}\<close> adjacent_V(2) adjacent_sym calculation insertCI)
      moreover have "adjacent v v2" using \<open>adjacent v v2\<close> .
      moreover have "adjacent v2 v1" using \<open>adjacent v1 v2\<close> adjacent_sym by auto
      moreover have "v1\<noteq>v" using \<open>v1 \<noteq> v\<close> .
      moreover have "v3\<noteq>v2" by (metis \<open>v3 \<notin> {v, v2}\<close> insert_subset subset_insertI)
      ultimately show False using no_quad[OF friend_assm] by auto
    qed
  thus "\<exists>v\<in>V. degree v G = 2" using \<open>v1\<in>V\<close> by auto
qed

lemma (in valid_unSimpGraph) regular:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E" and "finite V" and "\<not>(\<exists>v\<in>V. degree v G = 2)"
  shows "\<exists>k. \<forall>v\<in>V. degree v G = k"
proof -
  { fix v u assume "non_adj v u"  
    obtain v_adj where v_adj:"v_adj={n. adjacent v n}" by auto
    obtain u_adj where u_adj:"u_adj={n. adjacent u n}" by auto
    obtain f where f:"f = (\<lambda>n. (SOME v'. n\<in>V \<longrightarrow>n\<noteq>u\<longrightarrow>adjacent n v' \<and> adjacent u v'))" by auto
    have "\<And>n.  n\<in>V \<longrightarrow> n\<noteq>u \<longrightarrow> (\<exists>v'. adjacent n v' \<and> adjacent u v')" 
      proof (rule,rule)
        fix n assume  "n \<in> V" "n \<noteq> u" 
        hence "\<exists>!v'. adjacent n v' \<and> adjacent u v'" 
          using friend_assm[of n u] \<open>non_adj v u\<close> unfolding non_adj_def by auto
        thus "\<exists>v'. adjacent n v' \<and> adjacent u v'"  by auto
      qed
    hence f_ex:"\<And>n.  (\<exists>v'. n\<in>V \<longrightarrow> n\<noteq>u \<longrightarrow>  adjacent n v' \<and> adjacent u v')" by auto
    obtain v_adj_u where v_adj_u:"v_adj_u= f ` v_adj" by auto 
    have "finite u_adj" using u_adj adjacent_finite[OF \<open>finite E\<close>] by auto
    have "finite v_adj" using v_adj adjacent_finite[OF \<open>finite E\<close>] by auto
    hence "finite v_adj_u" using v_adj_u adjacent_finite[OF \<open>finite E\<close>] by auto
    have "inj_on f v_adj" unfolding inj_on_def
      proof (rule ccontr)
        assume "\<not> (\<forall>x\<in>v_adj. \<forall>y\<in>v_adj. f x = f y \<longrightarrow> x = y)"
        then obtain x y where "x\<in>v_adj" "y\<in>v_adj" "f x=f y" "x\<noteq>y" by auto
        have "x\<in>V" by (metis \<open>x \<in> v_adj\<close> adjacent_V(2) mem_Collect_eq v_adj)
        moreover have "x\<noteq>u" by (metis \<open>non_adj v u\<close> \<open>x \<in> v_adj\<close> mem_Collect_eq non_adj_def v_adj)
        ultimately have "adjacent (f x) u" and "adjacent x (f x)" 
          using someI_ex[OF f_ex[of x]] adjacent_sym by (metis f)+
        hence "f x \<noteq> v" by (metis \<open>non_adj v u\<close> non_adj_def)
        have "y\<in>V" by (metis \<open>y \<in> v_adj\<close> adjacent_V(2) mem_Collect_eq v_adj) 
        moreover have "y\<noteq>u" by (metis \<open>non_adj v u\<close> \<open>y \<in> v_adj\<close> mem_Collect_eq non_adj_def v_adj)
        ultimately have "adjacent y (f y)" using someI_ex[OF f_ex[of y]] by (metis f)
        hence " x \<noteq> y \<and> v \<noteq> f x \<and> adjacent v x \<and> adjacent x (f x) \<and> adjacent (f x) y 
            \<and> adjacent y v" 
          using \<open>x\<in>v_adj\<close> \<open>y\<in>v_adj\<close> \<open>f x=f y\<close> \<open>x\<noteq>y\<close> \<open>adjacent x (f x)\<close> v_adj adjacent_sym \<open>f x \<noteq> v\<close> 
          by auto
        thus False using no_quad[OF friend_assm] by auto
      qed
    then have "card v_adj =card v_adj_u" by (metis card_image v_adj_u)
    moreover have "v_adj_u \<subseteq> u_adj" 
      proof 
        fix x assume "x\<in>v_adj_u"
        then obtain y where "y\<in>v_adj" 
            and "x = (SOME v'. y \<in> V \<longrightarrow> y \<noteq> u \<longrightarrow> adjacent y v' \<and> adjacent u v')"
          using f image_def v_adj_u by auto
        hence "y \<in> V \<longrightarrow> y \<noteq> u \<longrightarrow> adjacent y x \<and> adjacent u x" using someI_ex[OF f_ex[of y]]
          by auto
        moreover have "y\<in>V" by (metis \<open>y \<in> v_adj\<close> adjacent_V(2) mem_Collect_eq v_adj) 
        moreover have "y\<noteq>u" by (metis \<open>non_adj v u\<close> \<open>y \<in> v_adj\<close> mem_Collect_eq non_adj_def v_adj)
        ultimately have "adjacent u x" by auto
        thus "x\<in>u_adj" unfolding u_adj by auto
      qed
    moreover have "card v_adj=degree v G" using degree_adjacent[OF \<open>finite E\<close>, of v] v_adj by auto
    moreover have "card u_adj=degree u G" using degree_adjacent[OF \<open>finite E\<close>, of u] u_adj by auto
    ultimately have "degree v G \<le> degree u G" using \<open>finite u_adj\<close> 
      by (metis \<open>inj_on f v_adj\<close> card_inj_on_le v_adj_u) }
  hence non_adj_degree:"\<And>v u. non_adj v u \<Longrightarrow> degree v G = degree u G" 
    by (metis adjacent_sym antisym non_adj_def)
  have "card V=3 \<Longrightarrow> ?thesis" 
    proof 
      assume "card V=3" 
      then obtain v1 v2 v3 where "V={v1,v2,v3}" "v1\<noteq>v2" "v2\<noteq>v3" "v1\<noteq>v3"
        proof -
          obtain v1 S1 where VS1:"V = insert v1 S1" and "v1 \<notin> S1"  and "card S1 = 2"
            using card_Suc_eq[of V 2] \<open>card V=3\<close> by auto
          then obtain v2 S2 where S1S2:"S1 = insert v2 S2" and "v2 \<notin> S2" and "card S2 = 1"
            using card_Suc_eq[of S1 1] by auto
          then obtain v3 where "S2={v3}"
            using card_Suc_eq[of S2 0] by auto
          hence "V={v1,v2,v3}" using VS1 S1S2 by auto
          moreover have "v1\<noteq>v2" "v2\<noteq>v3" "v1\<noteq>v3"using VS1 S1S2 \<open>v1\<notin>S1\<close> \<open>v2\<notin>S2\<close> \<open>S2={v3}\<close> by auto
          ultimately show ?thesis using that by auto
        qed
      obtain n where "adjacent v1 n" "adjacent v2 n" 
        using friend_assm[of v1 v2] by (metis \<open>V = {v1, v2, v3}\<close> \<open>v1 \<noteq> v2\<close> insertI1 insertI2)
      moreover hence "n=v3" 
        using \<open>V = {v1, v2, v3}\<close> adjacent_V(2) adjacent_no_loop 
        by (metis (mono_tags) empty_iff insertE)
      moreover obtain n' where "adjacent v2 n'" "adjacent v3 n'" 
        using friend_assm[of v2 v3] by (metis \<open>V = {v1, v2, v3}\<close> \<open>v2 \<noteq> v3\<close> insertI1 insertI2)
      moreover hence "n'=v1" 
        using \<open>V = {v1, v2, v3}\<close> adjacent_V(2) adjacent_no_loop
        by (metis (mono_tags) empty_iff insertE)
      ultimately have "adjacent v1 v2" and  "adjacent v2 v3" and "adjacent v3 v1" 
        using adjacent_sym by auto
      have "degree v1 G=2" 
        proof -
          have "v2\<in>{n. adjacent v1 n}" and "v3\<in>{n. adjacent v1 n}" and "v1\<notin>{n. adjacent v1 n}"
            using \<open>adjacent v1 v2\<close> \<open>adjacent v3 v1\<close> adjacent_sym 
            by (auto,metis adjacent_no_loop)
          hence "{n. adjacent v1 n}={v2,v3}" using \<open>V={v1,v2,v3}\<close> by auto 
            thus ?thesis using degree_adjacent[OF \<open>finite E\<close>,of v1] \<open>v2\<noteq>v3\<close> by auto
        qed
      moreover have "degree v2 G=2"
        proof -
          have "v1\<in>{n. adjacent v2 n}" and "v3\<in>{n. adjacent v2 n}" and "v2\<notin>{n. adjacent v2 n}"
            using \<open>adjacent v1 v2\<close> \<open>adjacent v2 v3\<close> adjacent_sym 
            by (auto,metis adjacent_no_loop)
          hence "{n. adjacent v2 n}={v1,v3}" using \<open>V={v1,v2,v3}\<close> by force 
            thus ?thesis using degree_adjacent[OF \<open>finite E\<close>,of v2] \<open>v1\<noteq>v3\<close> by auto 
        qed
      moreover have "degree v3 G=2"
        proof -
          have "v1\<in>{n. adjacent v3 n}" and "v2\<in>{n. adjacent v3 n}" and "v3\<notin>{n. adjacent v3 n}"
            using \<open>adjacent v3 v1\<close> \<open>adjacent v2 v3\<close> adjacent_sym 
            by (auto,metis adjacent_no_loop)
          hence "{n. adjacent v3 n}={v1,v2}" using \<open>V={v1,v2,v3}\<close> by force 
          thus ?thesis using degree_adjacent[OF \<open>finite E\<close>,of v3] \<open>v1\<noteq>v2\<close> by auto
        qed
      ultimately show "\<forall>v\<in>V. degree v G = 2" using \<open>V={v1,v2,v3}\<close> by auto
    qed
  moreover have "card V=2 \<Longrightarrow> False" 
    proof -
      assume "card V=2"
      obtain v1 v2 where "V={v1,v2}" "v1\<noteq>v2"
        proof -
          obtain v1 S1 where VS1:"V = insert v1 S1" and "v1 \<notin> S1" and "card S1 = 1" 
            using card_Suc_eq[of V 1] \<open>card V=2\<close> by auto
          then obtain v2 where "S1={v2}"
            using card_Suc_eq[of S1 0] by auto
          hence "V={v1,v2}" using VS1 by auto
          moreover have "v1\<noteq>v2" using \<open>v1\<notin>S1\<close> \<open>S1={v2}\<close> by auto
          ultimately show ?thesis using that by auto
        qed
      then obtain v3 where "adjacent v1 v3" "adjacent v2 v3" 
        using friend_assm[of v1 v2] by auto   
      hence "v3\<noteq>v2" and "v3\<noteq>v1" by (metis adjacent_no_loop)+
      hence "v3\<notin>V" using \<open>V={v1,v2}\<close> by auto
      thus False using \<open>adjacent v1 v3\<close> by (metis (full_types) adjacent_V(2))
    qed
  moreover have "card V=1 \<Longrightarrow> ?thesis" 
    proof 
      assume "card V=1"
      then obtain v1 where "V={v1}" using card_eq_SucD[of V 0] by auto
      have "E={}" 
        proof (rule ccontr) 
          assume "E\<noteq>{}"
          then obtain x1 x2 x3 where x:"(x1,x2,x3)\<in>E" by auto
          hence "x1=v1" and "x3=v1" using \<open>V={v1}\<close> E_validD by auto
          thus False using no_id x by auto
        qed
      hence "degree v1 G=0" unfolding degree_def by auto
      thus  "\<forall>v\<in>V. degree v G =0" using \<open>V={v1}\<close>by auto
    qed
  moreover have "card V=0 \<Longrightarrow> ?thesis"
    proof -
      assume "card V=0"
      hence "V={}" using \<open>finite V\<close> by auto
      thus ?thesis by auto
    qed
  moreover have "card V \<ge>4 \<Longrightarrow> \<not>(\<exists>v u. non_adj v u) \<Longrightarrow> False" 
    proof -
      assume "\<not>(\<exists>v u. non_adj v u)" "card V\<ge>4"
      hence non_non_adj:"\<And>v u. v\<notin>V \<or> u\<notin>V \<or> v=u \<or> adjacent v u" unfolding non_adj_def by auto
      obtain v1 v2 v3 v4 where "v1\<in>V" "v2\<in>V" "v3\<in>V" "v4\<in>V" "v1\<noteq>v2" "v1\<noteq>v3" "v1\<noteq>v4"
              "v2\<noteq>v3" "v2\<noteq>v4" "v3\<noteq>v4" 
        proof -
          obtain v1 B1 where "V = insert v1 B1"  "v1 \<notin> B1"  "card B1 \<ge>3"
            using \<open>card V\<ge>4\<close> card_le_Suc_iff[of 3 V] by auto
          then obtain v2 B2 where "B1 = insert v2 B2"  "v2 \<notin> B2"  "card B2 \<ge>2"
            using card_le_Suc_iff[of 2 B1] by auto
          then obtain v3 B3 where "B2= insert v3 B3" "v3\<notin>B3" "card B3\<ge>1"
            using card_le_Suc_iff[of 1 B2] by auto
          then obtain v4 B4 where "B3=insert v4 B4" "v4\<notin>B4" 
            using card_le_Suc_iff[of 0 B3] by auto
          have "v1\<in>V" by (metis \<open>V = insert v1 B1\<close> insert_subset order_refl)
          moreover have "v2\<in>V" 
            by (metis \<open>B1 = insert v2 B2\<close> \<open>V = insert v1 B1\<close> insert_subset subset_insertI)
          moreover have "v3\<in>V" 
            by (metis \<open>B1 = insert v2 B2\<close> \<open>B2 = insert v3 B3\<close> \<open>V = insert v1 B1\<close> insert_iff)
          moreover have "v4\<in>V" 
            by (metis \<open>B1 = insert v2 B2\<close> \<open>B2 = insert v3 B3\<close> \<open>B3 = insert v4 B4\<close> 
              \<open>V = insert v1 B1\<close> insert_iff)
          moreover have "v1\<noteq>v2" 
            by (metis (full_types) \<open>B1 = insert v2 B2\<close> \<open>v1 \<notin> B1\<close> insertI1)
          moreover have "v1\<noteq>v3" 
            by (metis \<open>B1 = insert v2 B2\<close> \<open>B2 = insert v3 B3\<close> \<open>v1 \<notin> B1\<close> insert_iff)
          moreover have "v1\<noteq>v4" 
            by (metis \<open>B1 = insert v2 B2\<close> \<open>B2 = insert v3 B3\<close> \<open>B3 = insert v4 B4\<close> \<open>v1 \<notin> B1\<close> 
              insert_iff)
          moreover have "v2\<noteq>v3" 
            by (metis (full_types) \<open>B2 = insert v3 B3\<close> \<open>v2 \<notin> B2\<close> insertI1)
          moreover have "v2\<noteq>v4" 
            by (metis \<open>B2 = insert v3 B3\<close> \<open>B3 = insert v4 B4\<close> \<open>v2 \<notin> B2\<close> insert_iff)
          moreover have "v3\<noteq>v4" 
            by (metis (full_types) \<open>B3 = insert v4 B4\<close> \<open>v3 \<notin> B3\<close> insertI1)
          ultimately show ?thesis using that by auto
        qed
      hence "adjacent v1 v2" using non_non_adj by auto
      moreover have "adjacent v2 v3" using non_non_adj by (metis \<open>v2 \<in> V\<close> \<open>v2 \<noteq> v3\<close> \<open>v3 \<in> V\<close>)
      moreover have "adjacent v3 v4" using non_non_adj by (metis \<open>v3 \<in> V\<close> \<open>v3 \<noteq> v4\<close> \<open>v4 \<in> V\<close>)
      moreover have "adjacent v4 v1" using non_non_adj by (metis \<open>v1 \<in> V\<close> \<open>v1 \<noteq> v4\<close> \<open>v4 \<in> V\<close>)
      ultimately show False using no_quad[OF friend_assm] 
        by (metis \<open>v1 \<noteq> v3\<close> \<open>v2 \<noteq> v4\<close>)
    qed  
  moreover have "card V\<ge>4 \<Longrightarrow> (\<exists>v u. non_adj v u) \<Longrightarrow> ?thesis" 
    proof - 
      assume "(\<exists>v u. non_adj v u)" "card V\<ge>4"
      then obtain v u where "non_adj v u" by auto
      then obtain w where "adjacent v w" and "adjacent u w" 
          and unique:"\<forall>n. adjacent v n \<and> adjacent u n \<longrightarrow> n=w"
        using friend_assm[of v u] unfolding non_adj_def by auto 
      have "\<forall>n\<in>V. degree n G = degree v G" 
        proof 
          fix n assume "n\<in>V"
          moreover have "n=v \<Longrightarrow> degree n G = degree v G" by auto
          moreover have "n=u \<Longrightarrow> degree n G = degree v G" 
            using non_adj_degree \<open>non_adj v u\<close> by auto
          moreover have "n\<noteq>v \<Longrightarrow> n\<noteq>u \<Longrightarrow> n\<noteq>w \<Longrightarrow> degree n G = degree v G" 
            proof -
              assume "n\<noteq>v" "n\<noteq>u" "n\<noteq>w"
              have "non_adj v n \<Longrightarrow> degree n G = degree v G" by (metis non_adj_degree)
              moreover have "non_adj u n \<Longrightarrow> degree n G = degree v G" 
                by (metis \<open>non_adj v u\<close> non_adj_degree)
              moreover have "\<not>non_adj u n \<Longrightarrow> \<not>non_adj v n \<Longrightarrow> degree n G = degree v G" 
                by (metis \<open>n \<in> V\<close> \<open>n \<noteq> w\<close> \<open>non_adj v u\<close> non_adj_def unique)
              ultimately show "degree n G = degree v G" by auto
            qed
          moreover have "n=w \<Longrightarrow> degree n G = degree v G" 
            proof -
              assume "n=w" 
              moreover have "\<not>(\<exists>v. \<forall>n\<in>V. n\<noteq>v \<longrightarrow> adjacent v n)" 
                using \<open>card V\<ge>4\<close> degree_two_windmill assms(2) assms(4) friend_assm
                by auto
              ultimately obtain w1 where "w1\<in>V" "w1\<noteq>w" "non_adj w w1"
                by (metis \<open>n\<in>V\<close> non_adj_def)
              have "w1=v \<Longrightarrow> degree n G = degree v G" 
                by (metis \<open>n = w\<close> \<open>non_adj w w1\<close> non_adj_degree)
              moreover have "w1=u \<Longrightarrow> degree n G = degree v G" 
                by (metis \<open>adjacent u w\<close> \<open>non_adj w w1\<close> adjacent_sym non_adj_def)
              moreover have "w1\<noteq>u \<Longrightarrow> w1\<noteq>v \<Longrightarrow> degree n G = degree v G" 
                by (metis \<open>n = w\<close> \<open>non_adj v u\<close> \<open>non_adj w w1\<close> non_adj_def non_adj_degree unique)
              ultimately show "degree n G = degree v G" by auto
            qed
          ultimately show "degree n G = degree v G" by auto
        qed
      thus ?thesis by auto
    qed
  ultimately show ?thesis by force
qed 

(*In this section, combinatorial proofs for the Friendship Theorem differ from the algebraic ones.
The main difference between these two approaches is that combinatorial proofs show Lemma 
exist_degree_two by counting the number of paths while algebraic proofs show it by computing
the eigenvalue of adjacency matrices.*)
section\<open>Exclusive steps for combinatorial proofs\<close>

fun (in valid_unSimpGraph) adj_path:: "'v \<Rightarrow> 'v list \<Rightarrow>bool" where
  "adj_path v [] =  (v\<in>V)" 
  | "adj_path v (u#us)= (adjacent v u \<and> adj_path u us)"

lemma (in valid_unSimpGraph) adj_path_butlast:
  "adj_path v ps \<Longrightarrow> adj_path v (butlast ps)"
by (induct ps arbitrary:v,auto)

lemma (in valid_unSimpGraph) adj_path_V:
  "adj_path v ps \<Longrightarrow> set ps \<subseteq> V"
by (induct ps arbitrary:v, auto)

lemma (in valid_unSimpGraph) adj_path_V':
  "adj_path v ps \<Longrightarrow> v\<in> V"
by (induct ps arbitrary:v, auto)

lemma (in valid_unSimpGraph) adj_path_app:
  "adj_path v ps \<Longrightarrow> ps\<noteq>[] \<Longrightarrow> adjacent (last ps) u \<Longrightarrow> adj_path v (ps@[u])"
proof (induct ps arbitrary:v)
  case Nil 
  thus ?case by auto
next
  case (Cons x xs)
  thus ?case by (cases xs,auto)
qed


lemma (in valid_unSimpGraph) adj_path_app':
  "adj_path v (ps @ [q] ) \<Longrightarrow> ps \<noteq> [] \<Longrightarrow> adjacent (last ps) q"
proof (induct ps arbitrary:v)
  case Nil 
  thus ?case by auto
next
  case (Cons x xs)
  thus ?case by (cases xs,auto)
qed

lemma card_partition':
  assumes "\<forall>v\<in>A. card {n. R v n} = k" "k>0" "finite A" 
      "\<forall>v1 v2. v1\<noteq>v2 \<longrightarrow> {n. R v1 n} \<inter> {n. R v2 n}={}"
  shows "card (\<Union>v\<in>A. {n. R v n}) = k * card A"
proof -
  have "\<And>C. C \<in> (\<lambda>x. {n. R x n}) ` A \<Longrightarrow> card C = k"
    proof -
      fix C assume "C \<in> (\<lambda>x. {n. R x n}) ` A"
      show "card C=k" by (metis (mono_tags) \<open>C \<in> (\<lambda>x. {n. R x n}) ` A\<close> assms(1) imageE)
    qed
  moreover have "\<And>C1 C2. C1 \<in>(\<lambda>x. {n. R x n}) ` A  \<Longrightarrow> C2 \<in> (\<lambda>x. {n. R x n}) ` A \<Longrightarrow> C1 \<noteq> C2 
      \<Longrightarrow> C1 \<inter> C2 = {}"
    proof -
      fix C1 C2 assume "C1 \<in> (\<lambda>x. {n. R x n}) ` A"  "C2 \<in> (\<lambda>x. {n. R x n}) ` A"  "C1 \<noteq> C2"
      obtain v1 where "v1\<in>A" "C1={n. R v1 n}" by (metis \<open>C1 \<in> (\<lambda>x. {n. R x n}) ` A\<close> imageE)
      obtain v2 where "v2\<in>A" "C2={n. R v2 n}" by (metis \<open>C2 \<in> (\<lambda>x. {n. R x n}) ` A\<close> imageE)
      have "v1\<noteq>v2" by (metis \<open>C1 = {n. R v1 n}\<close> \<open>C1 \<noteq> C2\<close> \<open>C2 = {n. R v2 n}\<close>)
      thus "C1 \<inter> C2 ={}" by (metis \<open>C1 = {n. R v1 n}\<close> \<open>C2 = {n. R v2 n}\<close> assms(4))
    qed
  moreover have "\<Union>((\<lambda>x. {n. R x n}) ` A) = (\<Union>x\<in>A. {n. R x n})" by auto
  moreover have "finite ((\<lambda>x. {n. R x n}) ` A )" by (metis assms(3) finite_imageI)
  moreover have "finite (\<Union>((\<lambda>x. {n. R x n}) ` A))" by (metis (full_types) assms(1) 
    assms(2) assms(3) card_eq_0_iff finite_UN_I less_nat_zero_code)
  moreover have " card A = card ((\<lambda>x. {n. R x n}) ` A)" 
    proof -
      have "inj_on (\<lambda>x. {n. R x n}) A" unfolding inj_on_def
        using \<open>\<forall>v1 v2. v1\<noteq>v2 \<longrightarrow> {n. R v1 n} \<inter> {n. R v2 n}={}\<close> 
        by (metis assms(1) assms(2) card_empty inf.idem less_le)
      thus ?thesis by (metis card_image)
    qed
  ultimately show ?thesis using card_partition[of "(\<lambda>x. {n. R x n}) ` A"] by auto
qed

lemma (in valid_unSimpGraph) path_count:
  assumes k_adj:"\<And>v. v\<in>V \<Longrightarrow> card {n. adjacent v n} = k" and  "v\<in>V" and "finite V" and "k>0"
  shows "card {ps. length ps=l \<and> adj_path v ps}=k^l"
proof (induct l rule:nat.induct)  
  case zero
  have "{ps. length ps=0 \<and> adj_path v ps}={[]}" using \<open>v\<in>V\<close> by auto 
  thus ?case by auto
next
  case (Suc n)
  obtain ext where ext: "ext=(\<lambda>ps ps'.  ps'\<noteq>[] \<and> (butlast ps'=ps) \<and> adj_path v ps')" by auto
  have "\<forall>ps\<in>{ps. length ps = n \<and> adj_path v ps}. card {ps'. ext ps ps'} = k" 
    proof 
      fix ps assume "ps\<in>{ps. length ps = n \<and> adj_path v ps}"
      hence "adj_path v ps" and "length ps = n" by auto
      obtain qs where qs:"qs = {n. if ps=[] then adjacent v n else adjacent (last ps) n}" by auto
      hence "card qs = k" 
        proof (cases "ps=[]")
          case True
          thus ?thesis using qs k_adj[OF \<open>v\<in>V\<close>] by auto
        next
          case False
          have "last ps \<in> V" using adj_path_V by (metis False \<open>adj_path v ps\<close> last_in_set subsetD)
          thus ?thesis using k_adj[of "last ps"] False qs by auto
        qed
      obtain app where app:"app=(\<lambda>q. ps@[q])" by auto
      have "app ` qs = {ps'. ext ps ps'}" 
        proof -
          have "\<And>xs. xs\<in> app ` qs \<Longrightarrow> xs \<in> {ps'. ext ps ps'}" 
            proof (rule,cases "ps=[]")
              case True
              fix xs assume "xs\<in> app ` qs"
              then obtain q where "q\<in> qs" "app q=xs" by (metis imageE)
              hence  "adjacent v q" and "xs=ps@[q]" using qs app True by auto
              hence "adj_path v xs" 
                by (metis True adj_path.simps(1) adj_path.simps(2) adjacent_V(2) append_Nil)
              moreover have "butlast xs = ps" using  \<open>xs=ps@[q]\<close> by auto              
              ultimately show "ext ps xs" using ext \<open>xs=ps@[q]\<close> by auto
            next
              case False
              fix xs assume "xs\<in> app ` qs"
              then obtain q where "q\<in> qs" "app q=xs" by (metis imageE)
              hence  "adjacent (last ps) q" using qs app False by auto
              hence "adj_path v (ps@[q])" using  \<open>adj_path v ps\<close> False adj_path_app by auto  
              hence "adj_path v xs" by (metis \<open>app q = xs\<close> app)
              moreover have "butlast xs=ps" by (metis \<open>app q = xs\<close> app butlast_snoc)
              ultimately show "ext ps xs" by (metis False butlast.simps(1) ext) 
            qed
          moreover have "\<And>xs. xs\<in>{ps'. ext ps ps'} \<Longrightarrow> xs\<in> app ` qs" 
            proof (cases "ps=[]")
              case True
              hence "qs = {n. adjacent v n }" using qs by auto
              fix xs assume "xs \<in> {ps'. ext ps ps'}" 
              hence "xs\<noteq>[]" and "(butlast xs=ps)" and "adj_path v xs" using ext by auto
              thus "xs \<in> app ` qs" 
                using True app \<open>qs = {n. adjacent v n}\<close>
                by (metis  adj_path.simps(2) append_butlast_last_id append_self_conv2 image_iff 
                  mem_Collect_eq)
            next
              case False
              fix xs assume "xs \<in> {ps'. ext ps ps'}" 
              hence "xs\<noteq>[]" and "(butlast xs=ps)" and "adj_path v xs" using ext by auto
              then obtain q where "xs=ps@[q]" by (metis append_butlast_last_id)
              hence "adjacent (last ps) q" using \<open>adj_path v xs\<close> False adj_path_app' by auto
              thus "xs \<in> app ` qs" using qs 
                by (metis (lifting, full_types) False \<open>xs = ps @ [q]\<close> app imageI mem_Collect_eq)
            qed
          ultimately show ?thesis by auto
        qed
      moreover have "inj_on app qs" using app unfolding inj_on_def by auto 
      ultimately show "card {ps'. ext ps ps'}=k" by (metis \<open>card qs = k\<close> card_image)
    qed
  moreover have "\<forall>ps1 ps2. ps1\<noteq>ps2 \<longrightarrow> {n. ext ps1 n} \<inter> {n. ext ps2 n}={}" using ext by auto
  moreover have "finite {ps. length ps = n \<and> adj_path v ps}"
    using Suc.hyps assms by (auto intro: card_ge_0_finite)
  ultimately have "card (\<Union>v\<in>{ps. length ps = n \<and> adj_path v ps}. {n. ext v n}) 
      = k * card {ps. length ps = n \<and> adj_path v ps}" 
    using card_partition'[of "{ps. length ps = n \<and> adj_path v ps}" ext k] \<open>k>0\<close> by auto 
  moreover have "{ps. length ps = n+1 \<and> adj_path v ps}
      =(\<Union>ps\<in>{ps. length ps = n \<and> adj_path v ps}. {ps'. ext ps ps'})" 
    proof -
      have "\<And>xs. xs \<in> {ps. length ps = n + 1 \<and> adj_path v ps} \<Longrightarrow> 
          xs \<in> (\<Union>ps\<in>{ps. length ps = n \<and> adj_path v ps}. {ps'. ext ps ps'})"
        proof -
          fix xs assume "xs \<in> {ps. length ps = n + 1 \<and> adj_path v ps}"
          hence "length xs = n +1" and "adj_path v xs" by auto
          hence "butlast xs \<in>{ps. length ps = n \<and> adj_path v ps}" 
            using adj_path_butlast length_butlast mem_Collect_eq by auto
          thus "xs \<in> (\<Union>ps\<in>{ps. length ps = n \<and> adj_path v ps}. {ps'. ext ps ps'})"
            using \<open>adj_path v xs\<close> \<open>length xs = n + 1\<close> UN_iff  ext length_greater_0_conv 
              mem_Collect_eq 
            by auto
        qed
      moreover have "\<And>xs . xs\<in>(\<Union>ps\<in>{ps. length ps = n \<and> adj_path v ps}. {ps'. ext ps ps'}) \<Longrightarrow>
          xs \<in> {ps. length ps = n + 1 \<and> adj_path v ps}"
        proof -
          fix xs assume "xs\<in>(\<Union>ps\<in>{ps. length ps = n \<and> adj_path v ps}. {ps'. ext ps ps'})"
          then obtain ys where "length ys=n" "adj_path v ys" "ext ys xs" by auto
          hence "length xs=n+1" using ext by auto
          thus "xs\<in>{ps. length ps = n + 1 \<and> adj_path v ps}" 
            by (metis (lifting, full_types) \<open>ext ys xs\<close> ext mem_Collect_eq)
        qed
      ultimately show ?thesis by fast
    qed
  ultimately show "card {ps. length ps = (Suc n) \<and> adj_path v ps} = k ^ (Suc n)" 
    using Suc.hyps by auto
qed

lemma (in valid_unSimpGraph) total_v_num:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n" 
      and "finite E" and "finite V" and "V\<noteq>{}" and " \<forall>v\<in>V. degree v G = k" and "k>0"
  shows "card V= k*k - k +1"
proof -
  have k_adj:"\<And>v. v\<in>V\<Longrightarrow>card ({n. adjacent v n})=k" by (metis assms(2) assms(5) degree_adjacent) 
  obtain v where "v\<in>V" using \<open>V\<noteq>{}\<close> by auto
  obtain l2_eq_v where l2_eq_v: "l2_eq_v={ps. length ps=2 \<and> adj_path v ps \<and> last ps=v}" by auto
  have "card l2_eq_v=k" 
    proof -
      obtain hds where hds:"hds= hd` l2_eq_v" by auto
      moreover have "hds={n. adjacent v n}" 
        proof -
          have "\<And>x. x\<in>hds \<Longrightarrow> x\<in> {n. adjacent v n}" 
            proof 
              fix x assume "x\<in>hds"
              then obtain ps where "hd ps=x" "length ps=2" "adj_path v ps" "last ps=v" 
                using hds l2_eq_v by auto
              thus "adjacent v x" 
                by (metis (full_types) adj_path.simps(2) list.sel(1) length_0_conv neq_Nil_conv 
                  zero_neq_numeral)
            qed
          moreover have "\<And>x. x\<in>{n. adjacent v n} \<Longrightarrow> x\<in>hds" 
            proof -
              fix x assume "x\<in>{n. adjacent v n}"
              obtain ps where "ps=[x,v]" by auto
              hence "hd ps=x" and "length ps=2" and "adj_path v ps" and "last ps=v"
                using \<open>x\<in>{n. adjacent v n}\<close> adjacent_sym by auto
              thus "x\<in>hds" by (metis (lifting, mono_tags) hds image_eqI l2_eq_v mem_Collect_eq)
            qed
          ultimately show "hds={n. adjacent v n}" by auto
        qed
      moreover have "inj_on hd l2_eq_v" unfolding inj_on_def 
        proof (rule+)
          fix x y assume "x \<in> l2_eq_v" "y \<in> l2_eq_v" "hd x = hd y"
          hence "length x=2" and "last x=last y" and "length y=2" 
            using l2_eq_v by auto
          hence "x!1=y!1" 
            using last_conv_nth[of x] last_conv_nth[of y] by force
          moreover have "x!0=y!0" 
            using \<open>hd x=hd y\<close> \<open>length x=2\<close> \<open>length y=2\<close>
            by(metis hd_conv_nth length_greater_0_conv)
          ultimately show "x=y" using \<open>length x=2\<close> \<open>length y=2\<close>
            using  nth_equalityI[of x y] 
            by (metis One_nat_def less_2_cases)
        qed
      ultimately show "card l2_eq_v=k" using k_adj[OF \<open>v\<in>V\<close>] by (metis card_image)
    qed
  obtain l2_neq_v where l2_neq_v:"l2_neq_v={ps. length ps=2 \<and> adj_path v ps \<and> last ps\<noteq>v}" by auto
  have "card l2_neq_v = k*k-k"
    proof -
      obtain l2_v where l2_v:"l2_v={ps. length ps=2\<and> adj_path v ps}" by auto
      hence "card l2_v=k*k" using path_count[OF k_adj,of v 2] \<open>0<k\<close> \<open>finite V\<close> \<open>v\<in>V\<close>
        by (simp add: power2_eq_square)
      hence "finite l2_v" using \<open>k>0\<close> by (metis card_infinite mult_is_0 neq0_conv) 
      moreover have "l2_v=l2_neq_v \<union> l2_eq_v" using l2_v l2_neq_v l2_eq_v by auto
      moreover have "l2_neq_v \<inter> l2_eq_v ={}" using l2_neq_v l2_eq_v by auto
      ultimately have "card l2_neq_v = card l2_v - card l2_eq_v"
        by (metis Int_commute Nat.add_0_right Un_commute card_Diff_subset_Int card_Un_Int
                  card_gt_0_iff diff_add_inverse finite_Diff finite_Un inf_sup_absorb
                  less_nat_zero_code)
      thus "card l2_neq_v = k*k-k" using \<open>card l2_eq_v=k\<close> using \<open>card l2_v=k*k\<close> by auto
    qed
  moreover have "bij_betw last l2_neq_v {n. n\<in>V \<and> n\<noteq>v}" 
    proof -
      have "last ` l2_neq_v = {n. n\<in>V \<and> n\<noteq>v}" 
        proof -
          have "\<And>x. x\<in> last` l2_neq_v \<Longrightarrow> x\<in>{n. n\<in>V \<and> n\<noteq>v}" 
            proof 
              fix x assume "x\<in>last` l2_neq_v"
              then obtain ps where "length ps = 2"  "adj_path v ps" "last ps=x" "last ps\<noteq>v"
                using l2_neq_v by auto
              hence "(last ps)\<in>V" 
                by (metis (full_types) adj_path_V last_in_set length_0_conv rev_subsetD 
                  zero_neq_numeral) 
              thus " x \<in> V \<and> x \<noteq> v" using \<open>last ps=x\<close> \<open>last ps\<noteq>v\<close> by auto
            qed
          moreover have "\<And>x. x\<in>{n. n\<in>V \<and> n\<noteq>v} \<Longrightarrow> x\<in> last` l2_neq_v" 
            proof -
              fix x assume x:"x \<in> {n \<in> V. n \<noteq> v}" 
              then obtain y where "adjacent v y" "adjacent x y"
                using friend_assm[of v x] \<open>v\<in>V\<close> by auto
              hence "adj_path v [y,x]" using adjacent_sym[of x y]by auto
              hence "[y,x]\<in>l2_neq_v"  using l2_neq_v x by auto
              thus "x\<in> last` l2_neq_v" by (metis imageI last.simps not_Cons_self2)
            qed
          ultimately show ?thesis by fast
        qed
      moreover have "inj_on last l2_neq_v" unfolding inj_on_def 
        proof (rule,rule,rule)
          fix x y assume "x \<in> l2_neq_v"  "y \<in> l2_neq_v"  "last x = last y"
          hence "length x=2" and "adj_path v x" and "last x\<noteq>v" and "length y=2" and "adj_path v y"
              and "last y\<noteq>v"
            using l2_neq_v by auto
          obtain x1 x2 y1 y2 where x:"x=[x1,x2]" and y:"y=[y1,y2]" 
            proof -
              { fix l assume "length l=2"
                obtain h1 t where "l=h1#t" and "length t=1"
                  using \<open>length l=2\<close> Suc_length_conv[of 1 l] by auto
                then obtain h2 where "t=[h2]"
                  using Suc_length_conv[of 0 t] by auto
                have "\<exists>h1 h2. l=[h1,h2]" using \<open>l=h1#t\<close> \<open>t=[h2]\<close> by auto }
              thus ?thesis using that \<open>length x=2\<close> \<open>length y=2\<close> by metis
            qed
          hence "x2\<noteq>v" and "y2\<noteq>v" using \<open>last x\<noteq>v\<close> \<open>last y\<noteq>v\<close> by auto
          moreover have "adjacent v x1" and "adjacent x2 x1" and "x2\<in>V"
            using \<open>adj_path v x\<close> x adjacent_sym by auto
          moreover have "adjacent v y1" and "adjacent y2 y1" and "y2\<in>V"
            using \<open>adj_path v y\<close> y adjacent_sym by auto
          ultimately have "x1=y1" using friend_assm \<open>v\<in>V\<close> 
            by (metis \<open>last x = last y\<close> last_ConsL last_ConsR not_Cons_self2 x y)
          thus "x=y" using x y \<open>last x = last y\<close> by auto
        qed
      ultimately show ?thesis unfolding bij_betw_def by auto
    qed
  hence "card l2_neq_v = card {n. n\<in>V \<and> n\<noteq>v}" by (metis bij_betw_same_card)
  ultimately have "card {n. n\<in>V \<and> n\<noteq>v}=k*k-k" by auto
  moreover have "card V = card {n. n\<in>V\<and>n\<noteq>v} + card {v}"
    proof -
      have "V={n. n\<in>V \<and> n\<noteq>v} \<union> {v}" using \<open>v\<in>V\<close> by auto
      moreover have "{n. n\<in>V \<and> n\<noteq>v} \<inter> {v}={}" by auto
      ultimately show ?thesis
        using \<open>finite V\<close> card_Un_disjoint[of "{n \<in> V. n \<noteq> v}" "{v}"] finite_Un
        by auto
    qed 
  ultimately show "card V = k*k-k+1" by auto
qed

lemma rotate_eq:"rotate1 xs=rotate1 ys \<Longrightarrow> xs=ys" 
proof (induct xs arbitrary:ys)
  case Nil
  thus ?case by (metis rotate1_is_Nil_conv)
next
  case (Cons n ns)
  hence "ys\<noteq>[]" by (metis list.distinct(1) rotate1_is_Nil_conv)
  thus "?case" using Cons by (metis butlast_snoc last_snoc list.exhaust rotate1.simps(2))
qed
  

lemma rotate_diff:"rotate m xs=rotate n xs \<Longrightarrow>rotate (m-n) xs = xs"
proof (induct m arbitrary:n)
  case 0
  thus ?case by auto
next 
  case (Suc m')
  hence "n=0 \<Longrightarrow> ?case" by auto
  moreover have "n\<noteq>0 \<Longrightarrow>?case" 
    proof -
      assume "n\<noteq>0" 
      then obtain n' where n': "n = Suc n'" by (metis nat.exhaust)
      hence "rotate m' xs = rotate n' xs" 
        using \<open>rotate (Suc m') xs = rotate n xs\<close> rotate_eq rotate_Suc 
        by auto
      hence "rotate (m' - n') xs = xs" by (metis Suc.hyps) 
      moreover have "Suc m' - n = m'-n'"
        by (metis n' diff_Suc_Suc) 
      ultimately show ?case by auto
    qed
  ultimately show ?case by fast 
qed    

lemma (in valid_unSimpGraph) exist_degree_two:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite E" and "finite V" and "card V\<ge>2" 
  shows "\<exists>v\<in>V. degree v G = 2"
proof (rule ccontr)
  assume "\<not> (\<exists>v\<in>V. degree v G = 2)"
  hence "\<And>v. v\<in>V \<Longrightarrow> degree v G\<noteq>2" by auto
  obtain k where k_adj: "\<And>v. v\<in>V\<Longrightarrow> card {n. adjacent v n}=k" using regular[OF friend_assm] 
    by (metis \<open>\<not> (\<exists>v\<in>V. degree v G = 2)\<close> assms(2) assms(3) degree_adjacent)
  have "k\<ge>4"
    proof -
      obtain v1 v2 where "v1\<in>V" "v2\<in>V" "v1\<noteq>v2"
        using \<open>card V\<ge>2\<close> by (metis \<open>\<not>(\<exists>v\<in>V. degree v G = 2)\<close> assms(2) degree_two_windmill)
      have "k\<noteq>0"
        proof 
          assume "k=0"
          obtain v3 where "adjacent v1 v3" using friend_assm[OF \<open>v1\<in>V\<close> \<open>v2\<in>V\<close> \<open>v1\<noteq>v2\<close>] by auto
          hence "card {n. adjacent v1 n} \<noteq> 0" using adjacent_finite[OF \<open>finite E\<close>] by auto
          moreover have "card {n. adjacent v1 n} = 0" using k_adj[OF \<open>v1\<in>V\<close>] 
            by (metis \<open>k = 0\<close>)
          ultimately show False by simp
        qed
      moreover have "even k" using even_degree[OF friend_assm] 
        by (metis \<open>v1 \<in> V\<close> assms(2) degree_adjacent k_adj)
      hence "k\<noteq>1" and "k\<noteq>3" by auto
      moreover have "k\<noteq>2" using \<open>\<And>v. v\<in>V \<Longrightarrow> degree v G\<noteq>2\<close> degree_adjacent k_adj 
        by (metis \<open>v1 \<in> V\<close> assms(2))  
      ultimately show ?thesis by auto
    qed
  obtain T where T:"T=(\<lambda>l::nat. {ps. length ps = l+1 \<and> adj_path (hd ps) (tl ps)})" by auto
  have T_count:"\<And>l::nat. card (T l) = (k*k-k+1)*k^l" using card_partition'
    proof -
      fix l::nat
      obtain ext where ext:"ext=(\<lambda>v ps. adj_path v (tl ps) \<and> hd ps=v \<and> length ps=l+1)" by auto
      have "\<forall>v\<in>V. card {ps. ext v ps} = k^l" 
        proof 
          fix v assume "v \<in> V" 
          have "\<And>ps. ps\<in>tl ` {ps. ext v ps} \<Longrightarrow>  ps\<in>{ps. length ps=l \<and> adj_path v ps}" 
            proof -
              fix ps assume  "ps \<in> tl ` {ps. ext v ps}"
              then obtain ps' where "adj_path v (tl ps')" "hd ps'=v" "length ps'=l+1" "ps=tl ps'"
                using ext by auto
              hence "adj_path v ps" and "length ps=l" by auto
              thus "ps\<in>{ps. length ps=l \<and> adj_path v ps}" by auto
            qed
          moreover have "\<And>ps. ps\<in>{ps. length ps=l \<and> adj_path v ps} \<Longrightarrow> ps\<in> tl ` {ps. ext v ps}" 
            proof -
              fix ps assume "ps \<in> {ps. length ps = l \<and> adj_path v ps}"
              hence "length ps=l" and "adj_path v ps" by auto
              moreover obtain ps' where "ps'=v#ps" by auto
              ultimately have "adj_path v (tl ps')" and "hd ps'=v" and "length ps'=l+1" by auto
              thus "ps \<in> tl ` {ps. ext v ps}" 
                by (metis \<open>ps' = v # ps\<close> ext imageI mem_Collect_eq list.sel(3))
            qed
          ultimately have "tl ` {ps. ext v ps} = {ps. length ps=l \<and> adj_path v ps}" by fast
          moreover have "inj_on tl {ps. ext v ps}"  unfolding inj_on_def 
            proof (rule,rule,rule)
              fix x y assume "x \<in> Collect (ext v)"  "y \<in> Collect (ext v)"  "tl x = tl y"
              hence "hd x=hd y" and "x\<noteq>[]" and "y\<noteq>[]"using ext by auto
              thus "x=y" using \<open>tl x= tl y\<close> by (metis list.sel(1,3) list.exhaust)
            qed
          moreover have "card {ps. length ps=l \<and> adj_path v ps} = k^l" 
            using path_count[OF k_adj,of v l]  \<open>4 \<le> k\<close> \<open>v \<in> V\<close> assms(3)
            by auto
          ultimately show " card {ps. ext v ps} = k ^ l" by (metis card_image)
        qed
      moreover have "\<forall>v1 v2. v1 \<noteq> v2 \<longrightarrow> {n. ext v1 n} \<inter> {n. ext v2 n} = {}" using ext by auto
      moreover have "(\<Union>v\<in>V. {n. ext v n})=T l" 
        proof -
          have "\<And>ps. ps\<in>(\<Union>v\<in>V. {n. ext v n}) \<Longrightarrow> ps\<in>T l" using T
            proof -
              fix ps assume "ps\<in>(\<Union>v\<in>V. {n. ext v n})"
              then obtain v where "v\<in>V" "adj_path v (tl ps)" "hd ps = v" "length ps = l + 1"
                using ext by auto
              hence "length ps = l + 1" and  "adj_path (hd ps) (tl ps)" by auto
              thus "ps\<in>T l" using T by auto
            qed
          moreover have "\<And>ps. ps\<in>T l \<Longrightarrow> ps\<in>(\<Union>v\<in>V. {n. ext v n})" 
            proof -
              fix ps assume "ps\<in>T l"
              hence "length ps = l + 1" and  "adj_path (hd ps) (tl ps)" using T by auto
              moreover then obtain v where "v=hd ps" "v\<in>V" 
                by (metis adj_path.simps(1) adj_path.simps(2) adjacent_V(1) list.exhaust)
              ultimately show "ps\<in>(\<Union>v\<in>V. {n. ext v n})" using ext by auto
            qed
          ultimately show ?thesis by auto
        qed
      ultimately have "card (T l) = card V * k^l" 
        using card_partition'[of V ext "k^l"] \<open> 4 \<le> k \<close> assms(3) mult.commute nat_one_le_power
        by auto
      moreover have "card V=(k * k - k + 1)" 
        using total_v_num[OF friend_assm,of k] k_adj degree_adjacent \<open>finite E\<close> \<open>finite V\<close> 
          \<open>card V\<ge>2\<close> \<open>4 \<le> k\<close> card_gt_0_iff
        by force
      ultimately show "card (T l) = (k * k - k + 1) * k ^ l" by auto
    qed
  obtain C where C:"C=(\<lambda>l::nat. {ps. length ps = l+1 \<and> adj_path (hd ps) (tl ps) 
      \<and> adjacent (last ps) (hd ps)})" by auto
  obtain C_star where C_star:"C_star=(\<lambda>l::nat. {ps. length ps = l+1 \<and> adj_path (hd ps) (tl ps) 
      \<and> (last ps) = (hd ps)})" by auto
  have "\<And>l::nat. card (C (l+1)) = k* card (C_star l) + card (T l - C_star l)"
    proof -
      fix l::nat
      have "C (l+1) = {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> adjacent (last ps) (hd ps)
          \<and> last (butlast ps)=hd ps} \<union> {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
          adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}" using C by auto
      moreover have " {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> adjacent (last ps) (hd ps)
          \<and> last (butlast ps)=hd ps} \<inter> {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
          adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps} ={}" by auto
      moreover have "finite (C (l+1))" 
        proof -
          have "C (l+1) \<subseteq> T (l+1)" using C T by auto
          moreover have "(k * k - k + 1) * k ^ (l + 1)\<noteq>0" using \<open>k\<ge>4\<close> by auto
          hence "finite (T (l+1))" using T_count[of "l+1"] by (metis card_infinite) 
          ultimately show ?thesis by (metis finite_subset)
        qed
      ultimately have "card (C (l+1)) = card {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) 
          \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps} + card {ps. length ps = l+2 \<and> 
          adj_path (hd ps) (tl ps) \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}" 
        using card_Un_disjoint[of "{ps. length ps = l + 2 \<and> adj_path (hd ps) (tl ps) \<and> adjacent 
          (last ps) (hd ps) \<and> last (butlast ps) = hd ps}" "{ps. length ps = l + 2 \<and> adj_path (hd ps) 
          (tl ps) \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps) \<noteq> hd ps}"] finite_Un
        by auto
      moreover have "card {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) 
          \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps}=k * card (C_star l)" 
        proof -
          obtain ext where ext: "ext=(\<lambda>ps ps'.  ps'\<noteq>[] \<and> (butlast ps'=ps) 
              \<and> adj_path (hd ps') (tl ps'))" by auto
          have "\<forall>ps\<in>(C_star l). card {ps'. ext ps ps'} = k" 
            proof 
              fix ps assume "ps\<in>C_star l"
              hence "length ps = l + 1" and "adj_path (hd ps) (tl ps)" and "last ps = hd ps" 
                using C_star by auto
              obtain qs where qs:"qs={v. adjacent (last ps) v}" by auto
              obtain app where app:"app=(\<lambda>v. ps@[v])" by auto
              have "app ` qs = {ps'. ext ps ps'}" 
                proof -
                  have "\<And>x. x\<in>app`qs \<Longrightarrow> x\<in>{ps'. ext ps ps'}" 
                    proof 
                      fix x assume "x \<in> app ` qs"
                      then obtain y where "adjacent (last ps) y" "x=ps@[y]" using qs app by auto
                      moreover hence "adj_path (hd x) (tl x)" 
                        by (cases "tl ps = []", metis adj_path.simps(1) adj_path.simps(2) 
                          adjacent_V(2) append_Nil list.sel(1,3) hd_append snoc_eq_iff_butlast 
                          tl_append2, metis \<open>adj_path (hd ps) (tl ps)\<close> adj_path_app hd_append
                          last_tl list.sel(2) tl_append2)
                      ultimately show "ext ps x" using ext by (metis snoc_eq_iff_butlast)
                    qed
                  moreover have "\<And>x. x\<in>{ps'. ext ps ps'}\<Longrightarrow> x\<in> app`qs"
                    proof -
                      fix x  assume "x \<in> {ps'. ext ps ps'}" 
                      hence "x\<noteq>[]" and "butlast x=ps" and "adj_path (hd x) (tl x)" 
                        using ext by auto
                      have "adjacent (last ps) (last x)"
                        proof (cases "length ps=1")
                          case True
                          hence "length x=2" using \<open>butlast x=ps\<close> by auto
                          then obtain x1 t1 where "x=x1#t1" and "length t1=1" 
                            using Suc_length_conv[of 1 x] by auto
                          then obtain x2 where "t1=[x2]"
                            using Suc_length_conv[of 0 t1] by auto
                          have "x=[x1,x2]" using \<open>x=x1#t1\<close> \<open>t1=[x2]\<close> by auto
                          thus "adjacent (last ps) (last x)"
                             using \<open>adj_path (hd x) (tl x)\<close> \<open>butlast x=ps\<close> by auto
                        next
                          case False
                          hence "tl ps\<noteq>[]" 
                            by (metis \<open>length ps = l + 1\<close> add_0_iff add_diff_cancel_left' 
                              length_0_conv length_tl add.commute)
                          moreover have "adj_path (hd x) (tl ps @ [last x])"
                            using \<open>adj_path (hd x) (tl x)\<close> \<open>butlast x=ps\<close> \<open>x \<noteq> []\<close>
                            by (metis append_butlast_last_id calculation list.sel(2) tl_append2)
                          ultimately have "adjacent (last (tl ps)) (last x)" 
                            using adj_path_app'[of "hd x" "tl ps" "last x"]
                            by auto
                          thus "adjacent (last ps) (last x)" by (metis \<open>tl ps \<noteq> []\<close> last_tl)
                        qed
                      thus "x \<in> app ` qs" using app qs 
                        by (metis \<open>butlast x = ps\<close> \<open>x \<noteq> []\<close> append_butlast_last_id mem_Collect_eq 
                          rev_image_eqI)
                    qed
                  ultimately show ?thesis by auto
                qed
              moreover have "inj_on app qs" using app unfolding inj_on_def by auto 
              moreover have "last ps\<in>V" 
                using \<open>length ps = l + 1\<close>  \<open>adj_path (hd ps) (tl ps)\<close> adj_path_V 
                by (metis \<open>last ps = hd ps\<close> adj_path.simps(1) last_in_set last_tl subset_code(1))
              hence "card qs=k" using qs k_adj by auto
              ultimately show "card {ps'. ext ps ps'} = k" by (metis card_image)
            qed
          moreover have "finite (C_star l)" 
            proof -
              have "C_star l \<subseteq> T l" using C_star T by auto
              moreover have "(k * k - k + 1) * k ^ l\<noteq>0" using \<open>k\<ge>4\<close> by auto
              hence "finite (T l)" using T_count[of "l"] by (metis card_infinite) 
              ultimately show ?thesis by (metis finite_subset)
            qed
          moreover have "\<forall>ps1 ps2. ps1 \<noteq> ps2 \<longrightarrow> {ps'. ext ps1 ps'} \<inter> {ps'. ext ps2 ps'} = {}" 
            using ext by auto
          moreover have "(\<Union>ps\<in>(C_star l). {ps'. ext ps ps'}) = {ps. length ps = l+2 
              \<and> adj_path (hd ps) (tl ps) \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps}" 
            proof -
              have "\<And>x. x\<in>(\<Union>ps\<in>(C_star l). {ps'. ext ps ps'}) \<Longrightarrow> x\<in>{ps. length ps = l+2 
                  \<and> adj_path (hd ps) (tl ps) \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps}"
                proof 
                  fix x assume "x \<in> (\<Union>ps\<in>C_star l. {ps'. ext ps ps'})"
                  then obtain ps where "ps\<in>C_star l" "ext ps x" by auto
                  hence "length ps = l + 1" and "adj_path (hd ps) (tl ps)" and "last ps = hd ps" 
                      and "x \<noteq> []" and  "butlast x = ps" "adj_path (hd x) (tl x)" 
                    using C_star ext by auto
                  have "length x = l + 2" 
                    using \<open> butlast x = ps \<close> \<open> length ps = l + 1 \<close> length_butlast by auto
                  moreover have "adj_path (hd x) (tl x)" by (metis \<open>adj_path (hd x) (tl x)\<close>)
                  moreover have "adjacent (last x) (hd x)" 
                    proof -
                      have "length x\<ge>2" using \<open>length x=l+2\<close> by auto
                      hence "adjacent (last (butlast x)) (last x)" using \<open>adj_path (hd x) (tl x)\<close>
                        by (induct x,auto, metis adj_path.simps(2) append_butlast_last_id 
                          append_eq_Cons_conv, metis adj_path_app' append_butlast_last_id)
                      hence "adjacent (last ps) (last x)" using \<open>butlast x=ps\<close> by auto
                      hence "adjacent (hd ps) (last x)" using \<open>last ps=hd ps\<close> by auto
                      hence "adjacent (hd x) (last x)" 
                        using \<open>butlast x=ps\<close> \<open>length ps=l+1\<close>
                        by (cases x)  auto
                      thus ?thesis using adjacent_sym by auto
                    qed
                  moreover have "last (butlast x) = hd x" 
                    by (metis \<open>butlast x = ps\<close> \<open>last ps = hd ps\<close> \<open>x \<noteq> []\<close> adjacent_no_loop 
                      butlast.simps(2) calculation(3) list.sel(1) last_ConsL neq_Nil_conv)
                  ultimately show "length x = l + 2 \<and> adj_path (hd x) (tl x) 
                      \<and> adjacent (last x) (hd x) \<and> last (butlast x) = hd x"
                    by auto
                qed
              moreover have "\<And>x. x\<in>{ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) 
                  \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps} \<Longrightarrow>  
                  x\<in>(\<Union>ps\<in>(C_star l). {ps'. ext ps ps'})" 
                proof -
                  fix x assume "x\<in>{ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) 
                      \<and> adjacent (last ps) (hd ps) \<and> last (butlast ps)=hd ps}"
                  hence "length x=l+2" and "adj_path (hd x) (tl x)" and "adjacent (last x) (hd x)"
                      and "last (butlast x)=hd x" by auto
                  obtain ps where ps:"ps=butlast x" by auto
                  have "ps\<in>C_star l" 
                    proof -
                      have "length ps = l + 1" using ps \<open>length x=l+2\<close> by auto
                      moreover have "hd ps=hd x" 
                        using ps \<open>length x=l+2\<close> 
                        by (metis (full_types) \<open> adjacent (last x) (hd x) \<close> adjacent_no_loop 
                          append_Nil append_butlast_last_id butlast.simps(1) list.sel(1) hd_append2)
                      hence "adj_path (hd ps) (tl ps)" using adj_path_butlast 
                        by (metis \<open>adj_path (hd x) (tl x)\<close> butlast_tl ps)
                      moreover have "last ps = hd ps" 
                        by (metis \<open>hd ps = hd x\<close> \<open>last (butlast x) = hd x\<close> ps)
                      ultimately show ?thesis using C_star by auto
                    qed
                  moreover have "ext ps x" using ext 
                    by (metis \<open>adj_path (hd x) (tl x)\<close> \<open>adjacent (last x) (hd x)\<close> 
                      \<open>last (butlast x) = hd x\<close> adjacent_no_loop butlast.simps(1) ps)
                  ultimately show "x\<in>(\<Union>ps\<in>(C_star l). {ps'. ext ps ps'})" by auto
                qed
              ultimately show ?thesis by fast
            qed
          ultimately show ?thesis using card_partition'[of "C_star l" ext k] \<open>k\<ge>4\<close> by auto
        qed
      moreover have "card {ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
          adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}=card (T l - C_star l)" 
        proof -
          obtain app where app:"app=(\<lambda>ps. ps@[SOME n. adjacent (last ps) n \<and> adjacent (hd ps) n])"
            by auto
          have "\<And>x. x\<in>app`(T l - C_star l) \<Longrightarrow> x\<in>{ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
              adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}" 
            proof 
              fix x assume "x \<in> app ` (T l - C_star l)"
              then obtain ps where "length ps = l + 1" "adj_path (hd ps) (tl ps)" "last ps \<noteq> hd ps"
                  "x=app ps"
                using T C_star by auto
              hence "last ps\<in>V" 
                using adj_path_V[OF \<open>adj_path (hd ps) (tl ps)\<close>]
                by (cases ps) auto
              hence "\<exists>n. adjacent (last ps) n \<and> adjacent (hd ps) n"
                using adj_path_V'[OF \<open>adj_path (hd ps) (tl ps)\<close>] \<open>last ps\<noteq>hd ps\<close>  
                  friend_assm[of "last ps" "hd ps"]
                by auto
              moreover have "last x=(SOME n. adjacent (last ps) n \<and> adjacent (hd ps) n)"
                using app \<open>x=app ps\<close> by auto
              ultimately have "adjacent (last ps) (last x)" and "adjacent (hd ps) (last x)"
                using someI_ex by (metis (lifting))+ 
              have "hd x=hd ps" using \<open>x=app ps\<close> \<open>length ps=l+1\<close> app
                by (cases ps) auto
              have "length x = l + 2" using \<open>x=app ps\<close> \<open>length ps=l+1\<close> app by auto
              moreover have "adj_path (hd x) (tl x)" 
                proof -
                  have "last (tl ps)=last ps" using \<open>length ps=l+1\<close> 
                    by (metis \<open>last ps \<noteq> hd ps\<close> list.sel(1,3) last_ConsL last_tl neq_Nil_conv)
                  moreover have "length ps\<noteq>1" using \<open>last ps \<noteq> hd ps\<close> 
                    by (metis Suc_eq_plus1_left gen_length_code(1) gen_length_def list.sel(1) 
                      last_ConsL length_Suc_conv neq_Nil_conv)
                  hence "tl ps\<noteq>[]" using \<open>length ps=l+1\<close> 
                    by(auto simp: length_Suc_conv)
                  ultimately have "adj_path (hd ps) (tl ps @ [last x])"
                    using  adj_path_app[OF \<open>adj_path (hd ps) (tl ps)\<close>,of "last x"]  
                      \<open>adjacent (last ps) (last x)\<close>  
                    by auto
                  moreover have "tl ps @ [last x]=tl x" 
                    using \<open>x=app ps\<close> app
                    by (metis \<open> last x = (SOME n. adjacent (last ps) n \<and> adjacent (hd ps) n) \<close> 
                      \<open> tl ps \<noteq> [] \<close> list.sel(2) tl_append2)
                  ultimately show ?thesis using \<open>hd x=hd ps\<close> by auto
                qed
              moreover have "adjacent (last x) (hd x)" 
                using \<open>hd x=hd ps\<close> \<open>adjacent (hd ps) (last x)\<close> adjacent_sym by auto
              moreover have "last (butlast x) \<noteq> hd x" 
                using \<open>last ps \<noteq> hd ps\<close> \<open>hd x=hd ps\<close>
                by (metis \<open>x = app ps\<close> app butlast_snoc)
              ultimately show "length x = l + 2 \<and> adj_path (hd x) (tl x) \<and> adjacent (last x) (hd x) 
                  \<and> last (butlast x) \<noteq> hd x"
                by auto
            qed
          moreover have "\<And>x. x\<in>{ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
              adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}\<Longrightarrow> x\<in>app`(T l - C_star l)"
            proof -
              fix x assume "x\<in>{ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
                  adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}"
              hence "length x=l+2" and "adj_path (hd x) (tl x)" and "adjacent (last x) (hd x)"
                  and "last (butlast x)\<noteq>hd x"
                by auto
              hence "butlast x\<in>T l - C_star l"
                proof -
                  have "length (butlast x) = l + 1" 
                    using \<open>length x = l + 2\<close> length_butlast by auto
                  moreover have "hd (butlast x)=hd x" 
                    using \<open>length x=l+2\<close> 
                    by (metis append_butlast_last_id butlast.simps(1) calculation diff_add_inverse 
                      diff_cancel2 hd_append length_butlast add.commute num.distinct(1) 
                      one_eq_numeral_iff)
                  hence "adj_path (hd (butlast x)) (tl (butlast x))" 
                    using \<open>adj_path (hd x) (tl x)\<close> by (metis adj_path_butlast butlast_tl)
                  moreover have "last (butlast x) \<noteq> hd (butlast x)" 
                    using \<open>last (butlast x)\<noteq>hd x\<close> \<open>hd (butlast x)=hd x\<close> by auto
                  ultimately show ?thesis using T C_star by auto
                qed
              moreover have "app (butlast x)=x" using app 
                proof -
                  have "last (butlast x)\<in>V" 
                    proof (cases "length x\<ge>3")
                      case True
                      hence "last (butlast x)\<in>set (tl x)"
                        proof (induct x)
                          case Nil
                          thus ?case by auto
                        next
                          case (Cons x1 t1)
                          have "length t1<3 \<Longrightarrow>?case" 
                            proof -
                              assume "length t1<3"
                              hence "length t1=2" using \<open>3 \<le> length (x1 # t1)\<close> by auto
                              then obtain x2 t2 where "t1=x2#t2" "length t2=1" 
                                using Suc_length_conv[of 1 t1] by auto
                              then obtain x3 where "t2=[x3]"
                                using  Suc_length_conv[of 0 t2] by auto
                              have "t1=[x2,x3]" using \<open>t1=x2#t2\<close> \<open>t2=[x3]\<close> by auto
                              thus ?case by auto
                            qed
                          moreover have "length t1\<ge>3\<Longrightarrow>?case"
                            proof -
                              assume "length t1\<ge>3"
                              hence "last (butlast t1) \<in> set (tl t1)" 
                                using Cons.hyps by auto
                              thus ?case 
                                by (metis butlast.simps(2) in_set_butlastD last.simps last_in_set 
                                  length_butlast length_greater_0_conv length_pos_if_in_set 
                                  length_tl list.sel(3))
                            qed
                          ultimately show ?case by force 
                        qed
                      thus ?thesis using adj_path_V[OF \<open>adj_path (hd x) (tl x)\<close>] by auto
                    next
                      case False
                      hence "length x=2" using \<open>length x=l+2\<close>  by auto
                      then obtain x1 x2 where "x=[x1,x2]" 
                        proof -
                          obtain x1 t1 where "x=x1#t1" "length t1=1" 
                            using Suc_length_conv[of 1 x] \<open>length x=2\<close> by auto
                          then obtain x2 where "t1=[x2]"
                            using  Suc_length_conv[of 0 t1] by auto
                          have "x=[x1,x2]" using \<open>x=x1#t1\<close> \<open>t1=[x2]\<close> by auto
                          thus ?thesis using that by auto
                        qed
                      hence "last (butlast x)=hd x" by auto
                      thus ?thesis using adj_path_V'[OF \<open>adj_path (hd x) (tl x)\<close>] by auto
                    qed
                  moreover have "hd (butlast x)=hd x" using \<open>length x=l+2\<close>
                    by (metis \<open>adjacent (last x) (hd x)\<close> adjacent_no_loop append_butlast_last_id 
                      butlast.simps(1) list.sel(1) hd_append)
                  hence  "hd (butlast x)\<in>V" using adj_path_V'[OF \<open>adj_path (hd x) (tl x)\<close>] by auto
                  moreover have "last (butlast x)\<noteq>hd (butlast x)" 
                    using \<open>last (butlast x)\<noteq>hd x\<close> \<open>hd (butlast x)=hd x\<close> by auto
                  ultimately have "\<exists>! n. adjacent (last (butlast x)) n \<and> adjacent (hd (butlast x)) n" 
                    using friend_assm by auto
                  moreover have "length x\<ge>2" using \<open>length x=l+2\<close> by auto
                  hence "adjacent (last (butlast x)) (last x)" 
                    using \<open>adj_path (hd x) (tl x)\<close> 
                    by (induct x,auto, metis (full_types) adj_path.simps(2) append_Nil 
                      append_butlast_last_id, metis adj_path_app' append_butlast_last_id)
                  moreover have "adjacent (hd (butlast x)) (last x)" 
                    using \<open>adjacent (last x) (hd x)\<close> \<open>hd (butlast x)=hd x\<close> adjacent_sym
                    by auto
                  ultimately have "(SOME n. adjacent (last (butlast x)) n 
                      \<and> adjacent (hd (butlast x)) n) = last x" 
                    using some1_equality by fast 
                  moreover have "x=(butlast x)@[last x]" 
                    by (metis \<open>adjacent (last (butlast x)) (last x)\<close> adjacent_no_loop 
                      append_butlast_last_id butlast.simps(1))
                  ultimately show ?thesis using app by auto
                qed
              ultimately show "x\<in>app`(T l - C_star l)" by (metis image_iff)  
            qed
          ultimately have "app`(T l - C_star l)={ps. length ps = l+2 \<and> adj_path (hd ps) (tl ps) \<and> 
              adjacent (last ps) (hd ps) \<and> last (butlast ps)\<noteq>hd ps}" by fast
          moreover have "inj_on app (T l - C_star l)" using app unfolding inj_on_def by auto
          ultimately show ?thesis by (metis card_image)
        qed
      ultimately show "card (C (l + 1)) = k * card (C_star l) + card (T l - C_star l)" by auto
    qed
  hence "\<And>l::nat. card (C (l+1)) mod (k-(1::nat))=1"
    proof -
      fix l::nat
      have "C_star l \<subseteq> T l" using C_star T by auto
      moreover have "card (T l)\<noteq>0" using T_count \<open>k\<ge>4\<close> by auto
      hence "finite (T l)" using \<open>k\<ge>4\<close> by (metis card_infinite)
      ultimately have "card (T l - C_star l)=card(T l) - card(C_star l)" 
        by (metis card_Diff_subset rev_finite_subset) 
      hence "card (C (l + 1))=k*card (C_star l) + (card (T l) - card (C_star l))" 
        using \<open>\<And>l::nat. card (C (l+1)) = k* card (C_star l) + card (T l - C_star l)\<close>
        by auto
      also have "...=k*card (C_star l) + card (T l) - card (C_star l)" 
        proof -
          have "card (T l) \<ge> card (C_star l)" 
            using \<open>C_star l \<subseteq> T l\<close> \<open>finite (T l)\<close> by (metis card_mono)
          thus ?thesis by auto
        qed
      also have "...=k*card (C_star l) - card (C_star l) + card (T l)" 
        proof -
          have "card (T l) \<ge> card (C_star l)" 
            using \<open>C_star l \<subseteq> T l\<close> \<open>finite (T l)\<close> by (metis card_mono)
          moreover have "k*card (C_star l) \<ge> card (C_star l)" using \<open>k\<ge>4\<close> by auto
          ultimately show ?thesis by auto
        qed
      also have "...=(k-(1::nat))*card(C_star l)+card(T l)" using \<open>k\<ge>4\<close> 
        by (metis monoid_mult_class.mult.left_neutral diff_mult_distrib)
      finally have "card (C (l + 1))=(k-(1::nat))*card(C_star l)+card(T l)" .
      hence "card (C (l+1)) mod (k-(1::nat)) = card(T l) mod (k-(1::nat))" using \<open>k>=4\<close> 
        by (metis mod_mult_self3 mult.commute)
      also have "...=((k*k-k+1)*k^l) mod (k-(1::nat))" using T_count by auto
      also have "...=((k-(1::nat))*k+1)*k^l  mod (k-(1::nat))" 
        proof -
          have "k*k-k+1=(k-(1::nat))*k+1" using \<open>k\<ge>4\<close> by (metis diff_mult_distrib nat_mult_1)
          thus ?thesis by auto
        qed
      also have "...=1*k^l  mod (k-(1::nat))" 
        by (metis mod_mult_right_eq mod_mult_self1 add.commute mult.commute)
      also have "...=k^l mod (k-(1::nat))" by auto
      also have "...=(k-(1::nat)+1)^l mod (k-(1::nat))" using \<open>k\<ge>4\<close> by auto
      also have "...=1^l mod (k-(1::nat))" by (metis mod_add_self2 add.commute power_mod)
      also have "...=1 mod (k-(1::nat))" by auto
      also have "...=1" using \<open>k\<ge>4\<close> by auto
      finally show "card (C (l+1)) mod (k-(1::nat)) =1" .
    qed
  obtain p::nat where "prime p" "p dvd (k-(1::nat))"  using \<open>k\<ge>4\<close> 
    by (metis Suc_eq_plus1 Suc_numeral add_One_commute eq_iff le_diff_conv numeral_le_iff  
      one_le_numeral one_plus_BitM prime_factor_nat semiring_norm(69) semiring_norm(71))
  hence p_minus_1:"p-(1::nat)+1=p" 
    by (metis add_diff_inverse add.commute not_less_iff_gr_or_eq prime_nat_iff)
  hence *: "\<And>l::nat. card (C (l+1)) mod p=1"
    using \<open>\<And>l::nat. card (C (l+1)) mod (k-(1::nat))=1\<close> mod_mod_cancel[OF \<open>p dvd (k-(1::nat))\<close>]
      \<open>prime p\<close>
    by (metis mod_if prime_gt_1_nat)
  have "card (C (p - 1)) mod p = 1"
  proof (cases "2 \<le> p")
    case True with * [of "p - 2"] show ?thesis
      by (metis Nat.add_diff_assoc2 add_le_cancel_right diff_diff_left one_add_one p_minus_1)
  next
    case False with * [of "p - 2"] \<open>prime p\<close> prime_ge_2_nat show ?thesis
      by blast
  qed
  moreover have "card (C (p-(1::nat))) mod p=0" using C
    proof -
      have closure1:"\<And>x. x\<in>C (p-(1::nat))\<Longrightarrow> rotate1 x \<in>C (p-(1::nat))" 
        proof -
          fix x assume "x\<in>C (p-(1::nat))"
          hence "length x = p" and  "adj_path (hd x) (tl x)" and "adjacent (last x) (hd x)" 
            using C p_minus_1 by auto
          have "adjacent (last (rotate1 x)) (hd (rotate1 x))" 
            proof -
              have "x\<noteq>[]" using \<open>length x=p\<close> \<open>prime p\<close> by auto
              hence "adjacent (last (rotate1 x)) (hd (rotate1 x))=adjacent (hd x) (hd (tl x))"
                by (metis \<open> adjacent (last x) (hd x) \<close> adjacent_no_loop append_Nil list.sel(1,3)
                  hd_append2 last_snoc list.exhaust rotate1_hd_tl)
              also have "...=True" using \<open>adj_path (hd x) (tl x)\<close> 
                using \<open>adjacent (last x) (hd x)\<close> \<open>x \<noteq> []\<close>
                by (metis  adj_path.simps(2) adjacent_no_loop append1_eq_conv append_Nil 
                  append_butlast_last_id list.sel(1,3) list.exhaust)
              finally show ?thesis by auto
            qed
          moreover have "adj_path (hd (rotate1 x)) (tl (rotate1 x))" 
            proof -
              have "x\<noteq>[]" using \<open>length x=p\<close> \<open>prime p\<close> by auto
              then obtain y ys where "y=hd x" "ys=tl x" by auto
              hence  "adj_path y ys" and "adjacent (last ys) y" and "ys\<noteq>[]" 
                by (metis \<open>adj_path (hd x) (tl x)\<close>, metis \<open>adjacent (last x) (hd x)\<close> \<open>y = hd x\<close> 
                  \<open>ys = tl x\<close> adjacent_no_loop list.sel(1,3) last.simps last_tl list.exhaust
                  , metis \<open>adjacent (last x) (hd x)\<close> \<open>x \<noteq> []\<close> \<open>ys = tl x\<close> adjacent_no_loop list.sel(1,3)
                  last_ConsL neq_Nil_conv)
              hence "adj_path (hd (rotate1 x)) (tl (rotate1 x))
                  =adj_path (hd (ys@[y])) (tl (ys@[y]))" 
                using \<open>x\<noteq>[]\<close> \<open>y=hd x\<close> \<open>ys=tl x\<close> by (metis rotate1_hd_tl)
              also have "...=adj_path (hd ys) ((tl ys)@[y])" 
                by (metis \<open>ys \<noteq> []\<close> hd_append tl_append2)
              also have "...=True" 
                using adj_path_app[OF \<open>adj_path y ys\<close> \<open>ys\<noteq>[]\<close> \<open>adjacent (last ys) y\<close>] \<open>ys\<noteq>[]\<close>
                by (metis adj_path.simps(2) append_Cons list.sel(1,3) list.exhaust)
              finally show ?thesis by auto
            qed
          moreover have "length (rotate1 x) = p" using \<open>length x=p\<close> by auto
          ultimately show "rotate1 x \<in> C (p-(1::nat))" using C p_minus_1 by auto
        qed
      have closure:"\<And>n x. x\<in>C (p-(1::nat))\<Longrightarrow> rotate n x \<in>C (p-(1::nat))" 
        proof -
          fix n x assume "x\<in>C (p-(1::nat))"
          thus "rotate n x \<in>C (p-(1::nat))"
            by (induct n,auto,metis One_nat_def closure1)
        qed
      obtain r where r:"r={(x,y). x\<in>C (p-(1::nat)) \<and> (\<exists>n<p. rotate n x=y)}" by auto 
      have "\<And>x. x\<in>C (p-(1::nat)) \<Longrightarrow> p dvd card {y.(\<exists>n<p. rotate n x=y)}"  
        proof -
          fix x assume "x \<in> C (p-(1::nat))"
          hence "length x=p" using C p_minus_1 by auto
          have "{y. (\<exists>n<p. rotate n x=y)}= (\<lambda>n. rotate n x)` {0..<p}" by auto
          moreover have "\<And>n1 n2. n1\<in>{0..<p} \<Longrightarrow> n2\<in>{0..<p} \<Longrightarrow> n1\<noteq>n2 \<Longrightarrow> rotate n1 x\<noteq>rotate n2 x" 
            proof 
              fix n1 n2 assume "n1 \<in> {0..<p}" "n2 \<in> {0..<p}" "n1 \<noteq> n2" "rotate n1 x = rotate n2 x"
              { fix n1 n2  
                assume "n1 \<in> {0..<p}" "n2 \<in> {0..<p}" "rotate n1 x = rotate n2 x" "n1>n2"
                obtain s::nat where "s*(n1-n2) mod p=1" "s>0" 
                  proof -
                    have "n1-n2>0" and "n1-n2<p" 
                      using \<open>n1 \<in> {0..<p}\<close> \<open>n2 \<in> {0..<p}\<close> \<open>n1>n2\<close> by auto
                    with \<open>prime p\<close> have "coprime (n1 - n2) p"
                      by (simp add: prime_nat_iff'' coprime_commute [of p])
                    then have "\<exists>x. [(n1 - n2) * x = 1] (mod p)"
                      by (simp add: cong_solve_coprime_nat)
                    then obtain s where "s * (n1 - n2) mod p = 1" 
                      using \<open>prime p\<close> prime_gt_1_nat [of p]
                      by (auto simp add: cong_def ac_simps)
                    moreover hence "s>0" by (metis mod_0 mult_0 neq0_conv zero_neq_one) 
                    ultimately show ?thesis using that by auto 
                  qed
                have "rotate (s*n1) x=rotate (s*n2) x" 
                  using \<open>rotate n1 x=rotate n2 x\<close>
                  apply (induct s)
                  apply (auto simp add: algebra_simps)
                  by (metis add.commute rotate_rotate)
                hence "rotate (s*n1 - s*n2) x= x" 
                  using rotate_diff by auto
                hence "rotate (s*(n1-n2)) x=x" by (metis diff_mult_distrib mult.commute)
                hence "rotate 1 x = x" using \<open>s*(n1-n2) mod p=1\<close> \<open>length x=p\<close> 
                  by (metis rotate_conv_mod) 
                hence "rotate1 x=x" by auto
                have "hd x=hd (tl x)" using \<open>prime p\<close> \<open>length x=p\<close> 
                  proof -
                    have "length x\<ge>2" using \<open>prime p\<close> \<open>length x=p\<close> using prime_ge_2_nat by blast 
                    hence "length (tl x)\<ge>1" by force
                    hence "x\<noteq>[]" and "tl x\<noteq>[]" by auto+
                    hence "x=(hd x)#(hd (tl x))#(tl (tl x))" using hd_Cons_tl by auto
                    hence "(hd (tl x))#(tl (tl x))@[hd x]=(hd x)#(hd (tl x))#(tl (tl x))"
                      using \<open>rotate1 x = x\<close> by (metis Cons_eq_appendI rotate1.simps(2))
                    thus ?thesis by auto
                  qed
                moreover have "hd x\<noteq>hd (tl x)"
                  proof -
                    have "adj_path (hd x) (tl x)" using \<open>x \<in> C (p-(1::nat))\<close> C by auto
                    moreover have "length x\<ge>2" using \<open>prime p\<close> \<open>length x=p\<close> using prime_ge_2_nat by blast
                    hence "length (tl x)\<ge>1" by force
                    hence "tl x\<noteq>[]" by force
                    ultimately have "adjacent (hd x) (hd (tl x))" 
                      by (metis adj_path.simps(2) list.sel(1) list.exhaust)
                    thus ?thesis by (metis adjacent_no_loop)
                  qed
                ultimately have False by auto } 
              thus False 
                by (metis \<open>n1 \<in> {0..<p}\<close> \<open>n1 \<noteq> n2\<close> \<open>n2 \<in> {0..<p}\<close> \<open>rotate n1 x = rotate n2 x\<close> 
                  less_linear)
            qed
          hence "inj_on (\<lambda>n. rotate n x) {0..<p}" unfolding inj_on_def by fast
          ultimately have "card {y. (\<exists>n<p. rotate n x=y)}=card {0..<p}" by (metis card_image) 
          hence "card {y. (\<exists>n<p. rotate n x=y)}=p" by auto
          thus "p dvd card {y. (\<exists>n<p. rotate n x=y)}" by auto
        qed
      hence "\<forall>X\<in>C (p-(1::nat)) // r. p dvd card X" unfolding quotient_def Image_def r by auto
      moreover have "refl_on (C (p - 1)) r" 
        proof -
          have "r \<subseteq> C (p - 1) \<times> C (p - 1)" 
            proof 
              fix x assume "x\<in>r"
              hence "fst x\<in>C (p - 1)" and "\<exists>n. snd x=rotate n (fst x)" using r by auto
              moreover then obtain n where "snd x=rotate n (fst x)" by auto
              ultimately have "snd x\<in>C (p - 1)" using closure by auto
              moreover have "x=(fst x,snd x)" using \<open>x\<in>r\<close> r by auto
              ultimately show  "x \<in> C (p - 1) \<times> C (p - 1)" using \<open>fst x\<in> C (p - 1)\<close> 
                by (metis SigmaI)
            qed
          moreover have "\<forall>x\<in>C (p - 1). (x, x) \<in> r" 
            proof 
              fix x assume "x \<in> C (p - 1)"
              hence "rotate 0 x \<in> C (p - 1)" using closure by auto
              moreover have "0<p" using \<open>prime p\<close> by (auto intro: prime_gt_0_nat)
              ultimately have "(x,rotate 0 x)\<in> r" using \<open>x\<in>C (p - 1 )\<close> r by auto
              moreover have "rotate 0 x=x" by auto
              ultimately show "(x,x)\<in>r" by auto
            qed
          ultimately show ?thesis using refl_on_def by auto
        qed
      moreover have "sym r" unfolding sym_def 
        proof (rule,rule,rule)
          fix x y assume "(x, y) \<in> r"
          hence "x\<in>C (p - 1)" using r by auto
          hence "length x=p" using C p_minus_1 by auto
          obtain n where "n<p" "rotate n x = y" using \<open>(x,y)\<in>r\<close> r by auto
          hence "y\<in> C (p - 1)" using closure[OF \<open>x\<in> C (p - 1)\<close>] by auto
          have "n=0\<Longrightarrow>(y, x) \<in> r" 
            proof -
              assume "n=0"
              hence "x=y" using \<open>rotate n x=y\<close> by auto
              thus "(y,x)\<in>r" using \<open>refl_on (C (p - 1)) r\<close> \<open>y \<in> C (p - 1)\<close> refl_on_def by fast
            qed
          moreover have "n\<noteq>0 \<Longrightarrow> (y,x)\<in>r" 
            proof -
              assume "n\<noteq>0"
              have "rotate (p-n) y = x" 
                proof -
                  have "rotate (p-n) y = rotate (p-n) (rotate n x)"
                    using \<open>rotate n x=y\<close> by auto
                  also have "rotate (p-n) (rotate n x)=rotate (p-n+n) x" 
                    using rotate_rotate by auto
                  also have "...=rotate p x" using \<open>n<p\<close> by auto
                  also have "...=rotate 0 x" using \<open>length x=p\<close> by auto
                  also have "...=x" by auto
                  finally show ?thesis .
                qed
              moreover have "p-n<p" using \<open>n<p\<close> \<open>n\<noteq>0\<close> by auto
              ultimately show "(y,x)\<in>r" using r \<open>y\<in> C (p - 1)\<close> by auto
            qed
          ultimately show "(y,x)\<in>r" by auto
        qed
      moreover have "trans r" unfolding trans_def
        proof (rule,rule,rule,rule,rule)
          fix x y z assume "(x, y) \<in> r" "(y, z) \<in> r"
          hence "x\<in>C (p - 1)" using r by auto
          hence "length x=p" using C p_minus_1 by auto
          obtain n1 n2 where "n1<p" "n2<p" "y=rotate n1 x" "z=rotate n2 y" 
            using r \<open>(x,y)\<in>r\<close> \<open>(y,z)\<in>r\<close> by auto
          hence "z=rotate (n2+n1) x" by (metis rotate_rotate)
          hence "z=rotate ((n2+n1) mod p) x" using \<open>length x=p\<close> by (metis rotate_conv_mod)
          moreover have "(n2+n1) mod p < p" by (metis \<open>prime p\<close> mod_less_divisor prime_gt_0_nat)
          ultimately show "(x,z)\<in>r" using \<open>x\<in> C (p - 1)\<close> r by auto 
        qed
      moreover have "finite (C (p - 1))" 
        by (metis \<open>card (C (p - 1)) mod p = 1\<close> card_eq_0_iff mod_0 zero_neq_one)
      ultimately have "p dvd card (C (p-(1::nat)))" using equiv_imp_dvd_card equiv_def by fast
      thus "card (C (p-(1::nat))) mod p=0" by (metis dvd_eq_mod_eq_0)
    qed 
  ultimately show False by auto
qed

theorem (in valid_unSimpGraph) friendship_thm:
  assumes friend_assm:"\<And>v u. v\<in>V \<Longrightarrow> u\<in>V \<Longrightarrow> v\<noteq>u \<Longrightarrow> \<exists>! n. adjacent v n \<and> adjacent u n"
      and "finite V" 
  shows "\<exists>v. \<forall>n\<in>V. n\<noteq>v \<longrightarrow> adjacent v n"    
proof -
  have "card V=0 \<Longrightarrow> ?thesis"
    using \<open>finite V\<close>
    by (metis all_not_in_conv card_seteq empty_subsetI le0)
  moreover have "card V=1 \<Longrightarrow> ?thesis" 
    proof -
      assume "card V=1"
      then obtain v where "V={v}" 
        using card_eq_SucD[of V 0] by auto
      hence "\<forall>n\<in>V. n=v" by auto
      thus "\<exists>v. \<forall>n\<in>V. n \<noteq> v \<longrightarrow> adjacent v n" by auto
    qed
  moreover have "card V\<ge>2 \<Longrightarrow> ?thesis" 
    proof -
      assume "card V\<ge>2"
      hence "\<exists>v\<in>V. degree v G = 2" 
        using exist_degree_two[OF friend_assm] \<open>finite V\<close> by auto
      thus ?thesis 
        using degree_two_windmill[OF friend_assm] \<open>card V\<ge>2\<close> \<open>finite V\<close> by auto
    qed
  ultimately show ?thesis by force
qed

end
