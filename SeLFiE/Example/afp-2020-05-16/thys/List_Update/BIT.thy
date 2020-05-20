(*  Title:       Competitive Analysis of BIT
    Author:      Max Haslbeck
*) 

section "BIT: an Online Algorithm for the List Update Problem"

theory BIT
imports
  Bit_Strings 
  MTF2_Effects
begin
    

abbreviation "config'' A qs init n == config_rand A init (take n qs)"


lemma sum_my: fixes f g::"'b \<Rightarrow> 'a::ab_group_add"
    assumes "finite A" "finite B"
  shows "(\<Sum>x\<in>A. f x) - (\<Sum>x\<in>B. g x)
    = (\<Sum>x\<in>(A \<inter> B). f x - g x) + (\<Sum>x\<in>A-B. f x) - (\<Sum>x\<in>B-A. g x)"
proof -
  have "finite (A-B)" and "finite (A\<inter>B)" and "finite (B-A)" and "finite (B\<inter>A)" using assms by auto 
  note finites=this
  have "(A-B) \<inter> ( (A\<inter>B)  ) = {}" and "(B-A) \<inter> ( (B\<inter>A)  ) = {}"  by auto
  note inters=this
  have commute: "A\<inter>B=B\<inter>A" by auto
  have "A = (A-B) \<union> (A\<inter>B)" and "B = (B-A) \<union> ( (B\<inter>A))"  by auto
  then have "(\<Sum>x\<in>A. f x) - (\<Sum>x\<in>B. g x) = (\<Sum>x\<in>(A-B) \<union> (A\<inter>B). f x) - (\<Sum>x\<in>(B-A) \<union> (B\<inter>A). g x)" by auto
  also have "\<dots> = ( (\<Sum>x\<in>(A-B). f x) + (\<Sum>x\<in>(A\<inter>B). f x) - (\<Sum>x\<in>(A-B)\<inter>(A\<inter>B). f x) )
        -( (\<Sum>x\<in>(B-A). g x) + (\<Sum>x\<in>(B\<inter>A). g x) - (\<Sum>x\<in>(B-A)\<inter>(B\<inter>A). g x))" 
          using sum_Un[where ?f="f",OF finites(1) finites(2)]
                sum_Un[where ?f="g",OF finites(3) finites(4)] by(simp)
  also have "\<dots> = ( (\<Sum>x\<in>(A-B). f x) + (\<Sum>x\<in>(A\<inter>B). f x) )
        - (\<Sum>x\<in>(B-A). g x) - (\<Sum>x\<in>(B\<inter>A). g x) " using inters by auto
  also have "\<dots> =  (\<Sum>x\<in>(A-B). f x) - (\<Sum>x\<in>(A\<inter>B). g x) + (\<Sum>x\<in>(A\<inter>B). f x) 
        - (\<Sum>x\<in>(B-A). g x)  " using commute by auto
  also have "\<dots> = (\<Sum>x\<in>(A\<inter>B). f x - g x) +(\<Sum>x\<in>(A-B). f x) 
        - (\<Sum>x\<in>(B-A). g x)" using sum_subtractf[of f g "(A\<inter>B)"] by auto
  finally show ?thesis .
qed

lemma sum_my2: "(\<forall>x\<in>A. f x = g x) \<Longrightarrow> (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. g x)" by auto


subsection "Definition of BIT" 


definition BIT_init :: "('a state,bool list * 'a list)alg_on_init" where
  "BIT_init init = map_pmf (\<lambda>l. (l,init)) (bv (length init))"



lemma "~ deterministic_init BIT_init"
unfolding deterministic_init_def BIT_init_def apply(auto)
apply(intro exI[where x="[a]"]) 
  \<comment> \<open>comment in a proof\<close>
by(auto simp: UNIV_bool set_pmf_bernoulli)
 
definition BIT_step :: "('a state, bool list * 'a list, 'a, answer)alg_on_step" where
"BIT_step s q = ( let a=((if (fst (snd s))!(index (snd (snd s)) q) then 0 else (length (fst s))),[]) in
                     return_pmf (a , (flip (index (snd (snd s)) q) (fst (snd s)), snd (snd s))))"
                 
lemma "deterministic_step BIT_step"
unfolding deterministic_step_def BIT_step_def
by simp



abbreviation BIT :: "('a state, bool list*'a list, 'a, answer)alg_on_rand" where
    "BIT == (BIT_init, BIT_step)"

 
subsection "Properties of BIT's state distribution"
 
lemma BIT_no_paid: "\<forall>((free,paid),_) \<in> (BIT_step s q). paid=[]"
unfolding BIT_step_def
by(auto)

subsubsection "About the Internal State"
term "(config'_rand (BIT_init, BIT_step) s0 qs) "
lemma config'_n_init: fixes qs init n
  shows "map_pmf (snd \<circ> snd) (config'_rand (BIT_init, BIT_step) init qs) = map_pmf (snd \<circ> snd) init"
apply (induct qs arbitrary: init)
  by (simp_all add: map_pmf_def bind_assoc_pmf BIT_step_def bind_return_pmf )   
 

lemma config_n_init: "map_pmf (snd \<circ> snd) (config_rand  (BIT_init, BIT_step) s0 qs) = return_pmf s0"
using config'_n_init[of "((fst (BIT_init, BIT_step) s0) \<bind> (\<lambda>is. return_pmf (s0, is)))"] 
  by (simp_all add: map_pmf_def bind_assoc_pmf  bind_return_pmf BIT_init_def )    

lemma config_n_init2: "\<forall>(_,(_,x)) \<in> set_pmf (config_rand (BIT_init, BIT_step) init qs). x = init"
proof (rule, goal_cases)
  case (1 z)
  then have 1: "snd(snd z) \<in> (snd \<circ> snd) ` set_pmf (config_rand   (BIT_init, BIT_step) init qs)"
        by force
  have "(snd \<circ> snd) ` set_pmf (config_rand  (BIT_init, BIT_step) init qs)
              = set_pmf (map_pmf (snd \<circ> snd) (config_rand  (BIT_init, BIT_step) init qs))" by(simp)
  also have "\<dots> = {init}" apply(simp only: config_n_init) by simp
  finally have "snd(snd z) = init" using 1 by auto 
  then show ?case by auto 
qed 
lemma config_n_init3: "\<forall>x \<in> set_pmf (config_rand (BIT_init, BIT_step) init qs). snd (snd x) = init"
using config_n_init2 by(simp add: split_def)



lemma config'_n_bv: fixes qs init n 
  shows " map_pmf (snd \<circ> snd) init = return_pmf s0
      \<Longrightarrow> map_pmf (fst \<circ> snd) init = bv (length s0)
      \<Longrightarrow> map_pmf (snd \<circ> snd) (config'_rand (BIT_init, BIT_step) init qs) = return_pmf s0
        \<and> map_pmf (fst \<circ> snd) (config'_rand (BIT_init, BIT_step) init qs) = bv (length s0)"
proof (induct qs arbitrary: init)
  case (Cons r rs) 
  from Cons(2) have a: "map_pmf (snd \<circ> snd) (init \<bind> (\<lambda>s. snd (BIT_init, BIT_step) s r \<bind>
           (\<lambda>(a, is'). return_pmf (step (fst s) r a, is'))))
            = return_pmf s0" apply(simp add: BIT_step_def)
              by (simp_all add: map_pmf_def bind_assoc_pmf BIT_step_def bind_return_pmf )  
  then have b: "\<forall>z\<in>set_pmf (init \<bind> (\<lambda>s. snd (BIT_init, BIT_step) s r \<bind>
           (\<lambda>(a, is'). return_pmf (step (fst s) r a, is')))). snd (snd z) = s0"
     by (metis (mono_tags, lifting) comp_eq_dest_lhs map_pmf_eq_return_pmf_iff)

  show ?case
    apply(simp only: config'_rand.simps)
    proof (rule Cons(1), goal_cases)  
      case 2
      have "map_pmf (fst \<circ> snd)
     (init \<bind>
      (\<lambda>s. snd (BIT_init, BIT_step) s r \<bind>
           (\<lambda>(a, is').
               return_pmf (step (fst s) r a, is')))) = map_pmf (flip (index s0 r)) (bv (length s0))" 
      using b
      apply(simp add: BIT_step_def Cons(3)[symmetric] bind_return_pmf map_pmf_def bind_assoc_pmf )
      apply(rule bind_pmf_cong)
        apply(simp)
        by(simp add: inv_flip_bv)
      also have "\<dots> = bv (length s0)"  using inv_flip_bv by auto
      finally show ?case  . 
   qed (fact)
qed simp

 
lemma config_n_bv_2: "map_pmf (snd \<circ> snd) (config_rand (BIT_init, BIT_step) s0 qs) = return_pmf s0
        \<and> map_pmf (fst \<circ> snd) (config_rand (BIT_init, BIT_step) s0 qs) = bv (length s0)"
apply(rule config'_n_bv)
  by(simp_all add: bind_return_pmf map_pmf_def bind_assoc_pmf bind_return_pmf' BIT_init_def)


 
lemma config_n_bv: "map_pmf (fst \<circ> snd) (config_rand (BIT_init, BIT_step) s0 qs) = bv (length s0)"
using config_n_bv_2 by auto

lemma config_n_fst_init_length: "\<forall>(_,(x,_)) \<in> set_pmf (config_rand (BIT_init, BIT_step) s0 qs). length x = length s0"
proof 
  fix x::"('a list \<times> (bool list \<times> 'a list))"
  assume ass:"x \<in> set_pmf (config_rand (BIT_init, BIT_step) s0 qs)" 
  let ?a="fst (snd x)"
  from ass have "(fst x,(?a,snd (snd x))) \<in> set_pmf (config_rand (BIT_init, BIT_step) s0 qs)" by auto
  with ass have "?a \<in> (fst \<circ> snd) ` set_pmf (config_rand (BIT_init, BIT_step) s0 qs)" by force
  then have "?a \<in> set_pmf (map_pmf (fst \<circ> snd) (config_rand (BIT_init, BIT_step) s0 qs))" by auto
  then have "?a \<in> bv (length s0)" by(simp only: config_n_bv)
  then have "length ?a = length s0" by (auto simp: len_bv_n)
  then show "case x of (uu_, xa, uua_) \<Rightarrow> length xa = length s0" by(simp add: split_def)
qed

lemma config_n_fst_init_length2: "\<forall>x \<in> set_pmf (config_rand (BIT_init, BIT_step) s0 qs). length (fst (snd x)) = length s0"
using config_n_fst_init_length by(simp add: split_def)



lemma fperms: "finite {x::'a list. length x = length init \<and> distinct x \<and> set x = set init}"
apply(rule finite_subset[where B="{xs. set xs \<subseteq> set init \<and> length xs \<le> length init}"])
apply(force) apply(rule finite_lists_length_le) by auto


lemma finite_config_BIT: assumes [simp]: "distinct init"
  shows "finite (set_pmf (config_rand (BIT_init, BIT_step) init qs))" (is "finite ?D")
proof -
  have a: "(fst \<circ> snd) ` ?D \<subseteq> {x. length x = length init}" using config_n_fst_init_length2 by force
  have c: "(snd \<circ> snd) ` ?D = {init}"
  proof -
    have "(snd \<circ> snd) ` set_pmf (config_rand (BIT_init, BIT_step) init qs)
                = set_pmf (map_pmf (snd \<circ> snd) (config_rand (BIT_init, BIT_step) init qs))" by(simp)
    also have "\<dots> = {init}" apply(subst config_n_init) by simp
    finally show ?thesis .
  qed
  from a c have d: "snd ` ?D \<subseteq> {x. length x = length init} \<times> {init}" by force
  have b: "fst ` ?D \<subseteq> {x. length x = length init \<and> distinct x \<and> set x = set init}"
    using config_rand by fastforce

  from b d have "?D \<subseteq> {x. length x = length init \<and> distinct x \<and> set x = set init} \<times> ({x. length x = length init} \<times> {init})"
   by auto
  then show ?thesis
    apply (rule finite_subset)
      apply(rule finite_cartesian_product)
        apply(rule fperms)
        apply(rule finite_cartesian_product)
          apply (rule bitstrings_finite)
          by(simp) 
qed


subsection "BIT is $1.75$-competitive (a combinatorial proof)"
 






subsubsection "Definition of the Locale and Helper Functions"
locale BIT_Off = 
fixes acts :: "answer list"  
fixes qs :: "'a list" 
fixes init :: "'a list" 
assumes dist_init[simp]: "distinct init"
assumes len_acts: "length acts = length qs"
begin


lemma setinit: "(index init) ` set init = {0..<length init}" 
using dist_init
proof(induct init)
  case (Cons a as)
  with Cons have iH: "index as ` set as = {0..<length as}" by auto
  from Cons have 1:"(set as \<inter> {x. (a \<noteq> x)}) = set as" by fastforce
  have 2: "(\<lambda>a. Suc (index as a)) ` set as =
          (\<lambda>a. Suc a) ` ((index as) ` set as )" by auto
  show ?case
  apply(simp add: 1 2 iH) by auto
qed simp

definition free_A :: "nat list" where      (* free exchanges of A *)
"free_A = map fst acts"

definition paid_A' :: "nat list list" where  (* paid exchanges of A' *)
"paid_A' = map snd acts"

definition paid_A  :: "nat list list" where  (* paid exchanges of A *)
  "paid_A  = map (filter (\<lambda>x. Suc x < length init)) paid_A'"

lemma len_paid_A[simp]: "length paid_A = length qs"
unfolding paid_A_def paid_A'_def using len_acts by auto
lemma len_paid_A'[simp]: "length paid_A' = length qs"
unfolding paid_A'_def using len_acts by auto


lemma paidAnm_inbound: "n < length paid_A \<Longrightarrow> m < length(paid_A!n) \<Longrightarrow> (Suc ((paid_A!n)!(length (paid_A ! n) - Suc m))) < length init"
proof -
  assume "n < length paid_A"
  then have "n < length paid_A'" by auto
  then have a: "(paid_A!n)
      = filter (\<lambda>x. Suc x < length init) (paid_A' ! n)" unfolding paid_A_def by auto 

  let ?filtered="(filter (\<lambda>x. Suc x < length init) (paid_A' ! n))"
  assume mtt: "m < length (paid_A!n)"
  with a have "(length (paid_A ! n) - Suc m) < length ?filtered" by auto
  with nth_mem have b: "Suc(?filtered ! (length (paid_A ! n) - Suc m)) < length init" by force

  show "Suc (paid_A ! n ! (length (paid_A ! n) - Suc m)) < length init" using a b by auto
qed

fun s_A' :: "nat \<Rightarrow> 'a list" where 
"s_A' 0 = init" |
"s_A'(Suc n) = step (s_A' n) (qs!n) (free_A!n, paid_A'!n)"

lemma length_s_A'[simp]: "length(s_A' n) = length init"
by (induction n) simp_all

lemma dist_s_A'[simp]: "distinct(s_A' n)" 
by(induction n) (simp_all add: step_def)

lemma set_s_A'[simp]: "set(s_A' n) = set init"
by(induction n) (simp_all add: step_def)

fun s_A  :: "nat \<Rightarrow> 'a list" where  
"s_A 0 = init" |
"s_A(Suc n) = step (s_A n) (qs!n) (free_A!n, paid_A!n)"

lemma length_s_A[simp]: "length(s_A n) = length init"
by (induction n) simp_all

lemma dist_s_A[simp]: "distinct(s_A n)" 
by(induction n) (simp_all add: step_def)

lemma set_s_A[simp]: "set(s_A n) = set init"
by(induction n) (simp_all add: step_def)

lemma cost_paidAA': "n < length paid_A' \<Longrightarrow> length (paid_A!n) \<le> length (paid_A'!n)"
  unfolding paid_A_def by simp

lemma swaps_filtered: "swaps (filter (\<lambda>x. Suc x < length xs) ys) xs = swaps (ys) xs"
apply (induct ys) by auto

lemma sAsA': "n < length paid_A' \<Longrightarrow> s_A' n = s_A n"
proof (induct n)
  case (Suc m) 
  have " s_A' (Suc m)
        =  mtf2 (free_A!m) (qs!m) (swaps (paid_A'!m) (s_A' m))" by (simp add: step_def) 
  also from Suc(2) have "\<dots> = mtf2 (free_A!m) (qs!m) (swaps (paid_A!m) (s_A' m))"
      unfolding paid_A_def                                   
      by (simp only: nth_map swaps_filtered[where xs="s_A' m", simplified])
  also have "\<dots> = mtf2 (free_A!m) (qs!m) (swaps (paid_A!m) (s_A m))" using Suc by auto
  also have "\<dots> = s_A (Suc m)" by (simp add: step_def)
  finally show ?case .
qed simp


lemma sAsA'': "n < length qs \<Longrightarrow> s_A n =  s_A' n"
using sAsA' by auto


definition t_BIT :: "nat \<Rightarrow> real" where   (* BIT's cost in nth step *)
"t_BIT n = T_on_rand_n BIT init qs n"

definition T_BIT :: "nat \<Rightarrow> real" where   (* BIT's cost in first n steps *)
"T_BIT n = (\<Sum>i<n. t_BIT i)"


definition c_A :: "nat \<Rightarrow> int" where 
"c_A n = index (swaps (paid_A!n) (s_A n)) (qs!n) + 1"

definition f_A :: "nat \<Rightarrow> int" where 
"f_A n = min (free_A!n) (index (swaps (paid_A!n) (s_A n)) (qs!n))"

definition p_A :: "nat \<Rightarrow> int" where  
"p_A n = size(paid_A!n)"

definition t_A :: "nat \<Rightarrow> int" where  
"t_A n = c_A n + p_A n"



definition c_A' :: "nat \<Rightarrow> int" where  
"c_A' n = index (swaps (paid_A'!n) (s_A' n)) (qs!n) + 1"

definition p_A' :: "nat \<Rightarrow> int" where 
"p_A' n = size(paid_A'!n)"
definition t_A' :: "nat \<Rightarrow> int"  where  
"t_A' n = c_A' n + p_A' n"
 
lemma t_A_A'_leq: "n < length paid_A' \<Longrightarrow> t_A n \<le> t_A' n"
unfolding t_A_def t_A'_def c_A_def c_A'_def p_A_def p_A'_def
  apply(simp add: sAsA')
  unfolding paid_A_def
  by (simp add: swaps_filtered[where xs="(s_A n)", simplified])

definition T_A' :: "nat \<Rightarrow> int" where 
"T_A' n = (\<Sum>i<n. t_A' i)"
                                                 
definition T_A :: "nat \<Rightarrow> int" where 
"T_A n = (\<Sum>i<n. t_A i)"
 
lemma T_A_A'_leq: "n \<le> length paid_A' \<Longrightarrow> T_A n \<le> T_A' n"
unfolding T_A'_def T_A_def apply(rule sum_mono)
by (simp add: t_A_A'_leq)

lemma T_A_A'_leq': "n \<le> length qs \<Longrightarrow> T_A n \<le> T_A' n"
using T_A_A'_leq by auto
 

fun s'_A :: "nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"s'_A n 0 = s_A n" 
| "(s'_A n (Suc m)) = swap ((paid_A  ! n)!(length (paid_A  ! n) -(Suc m)) ) (s'_A n m)"

lemma set_s'_A[simp]: "set (s'_A n m) = set init"
apply(induct m) by(auto)

lemma len_s'_A[simp]: "length (s'_A n m) = length init"
apply(induct m) by(auto)

lemma distperm_s'_A[simp]: "dist_perm (s'_A n m) init"
apply(induct m) by auto

lemma s'A_m_le: "m \<le> (length (paid_A ! n)) \<Longrightarrow> swaps (drop (length (paid_A  ! n) - m) (paid_A ! n)) (s_A n) = s'_A n m"
apply(induct m)
apply(simp)
proof -
  fix m
  assume iH: "(m \<le> length (paid_A ! n) \<Longrightarrow> swaps (drop (length (paid_A ! n) - m) (paid_A ! n)) (s_A n) = s'_A n m)"
  assume Suc: "Suc m \<le> length (paid_A ! n)"
  then have "m \<le> length (paid_A ! n)" by auto
  with iH have x: "swaps (drop (length (paid_A ! n) - m) (paid_A ! n)) (s_A n) = s'_A n m" by auto
  
  from Suc have mlen: "(length (paid_A ! n) - Suc m) < length (paid_A ! n)" by auto

  let ?l="length (paid_A ! n) - Suc m"
  let ?Sucl="length (paid_A ! n) - m"
  have Sucl: "Suc ?l = ?Sucl" using Suc by auto

  from mlen have yu:  "((paid_A  ! n)! ?l ) # (drop (Suc ?l) (paid_A ! n))
        = (drop ?l (paid_A ! n))" 
    by (rule Cons_nth_drop_Suc)

  from Suc have "s'_A n (Suc m)
      = swap ((paid_A  ! n)!(length (paid_A  ! n) - (Suc m)) ) (s'_A n m)" by auto
  also have "\<dots> = swap ((paid_A  ! n)!(length (paid_A  ! n) - (Suc m)) )
                    (swaps (drop (length (paid_A ! n) - m) (paid_A ! n)) (s_A n))"
    by(simp only: x)
  also have "\<dots> = (swaps (((paid_A  ! n)!(length (paid_A  ! n) - (Suc m)) ) # (drop (length (paid_A ! n) - m) (paid_A ! n))) (s_A n))"
    by auto
  also have "\<dots> = (swaps (((paid_A  ! n)! ?l ) # (drop (Suc ?l) (paid_A ! n))) (s_A n))"
    using Sucl by auto
  also from mlen have "\<dots> = (swaps ((drop ?l (paid_A ! n))) (s_A n))"
    by (simp only: yu)
  finally have " s'_A n (Suc m) = swaps (drop (length (paid_A ! n) - Suc m) (paid_A ! n)) (s_A n)" .
  then show " swaps (drop (length (paid_A ! n) - Suc m) (paid_A ! n)) (s_A n) = s'_A n (Suc m)" by auto
qed

lemma s'A_m: "swaps (paid_A ! n) (s_A n) = s'_A n (length (paid_A ! n))"
using s'A_m_le[of "(length (paid_A ! n))" "n", simplified] by auto

 
definition gebub :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gebub n m = index init ((s'_A n m)!(Suc ((paid_A!n)!(length (paid_A ! n) - Suc m))))"
 
lemma gebub_inBound: assumes 1: " n < length paid_A " and  2: "m < length (paid_A !  n)" 
          shows "gebub n m < length init"  
proof -
  have "Suc (paid_A ! n ! (length (paid_A ! n) - Suc m)) < length (s'_A n m)" using paidAnm_inbound[OF 1 2] by auto
  then have "s'_A n m ! Suc (paid_A ! n ! (length (paid_A ! n) - Suc m)) \<in> set (s'_A n m)" by (rule nth_mem)
  then show ?thesis
      unfolding gebub_def using setinit by auto
qed 
  

subsubsection "The Potential Function"
 
fun phi :: "nat \<Rightarrow>'a list\<times>  (bool list \<times> 'a list)  \<Rightarrow> real" ("\<phi>")  where
"phi n (c,(b,_)) = (\<Sum>(x,y)\<in>(Inv c (s_A n)). (if b!(index init y) then 2 else 1))"

lemma phi': "phi n z = (\<Sum>(x,y)\<in>(Inv (fst z) (s_A n)). (if (fst (snd z))!(index init y) then 2 else 1))"
proof -
  have "phi n z = phi n (fst z, (fst(snd z),snd(snd z)))" by (metis prod.collapse)
  also have "\<dots> = (\<Sum>(x,y)\<in>(Inv (fst z) (s_A n)). (if (fst (snd z))!(index init y) then 2 else 1))" by(simp del: prod.collapse)
  finally show ?thesis .
qed

lemma Inv_empty2: "length d = 0 \<Longrightarrow> Inv c d = {}"
unfolding Inv_def before_in_def by(auto)

corollary Inv_empty3: "length init = 0 \<Longrightarrow> Inv c (s_A n) = {}"
apply(rule Inv_empty2) by (metis length_s_A)

lemma phi_empty2: "length init = 0 \<Longrightarrow> phi n (c,(b,i)) = 0"
apply(simp only: phi.simps Inv_empty3) by auto

lemma phi_nonzero: "phi n (c,(b,i)) \<ge> 0"
by (simp add: sum_nonneg split_def)

(* definition of the potential function! *)
definition Phi :: "nat \<Rightarrow> real" ("\<Phi>") where
"Phi n = E( map_pmf (\<phi> n) (config'' BIT qs init n))"

definition PhiPlus :: "nat \<Rightarrow> real" ("\<Phi>\<^sup>+") where
"PhiPlus n = (let
        nextconfig = bind_pmf (config'' BIT qs init n)
                (\<lambda>(s,is). bind_pmf  (BIT_step (s,is) (qs!n)) (\<lambda>(a,nis). return_pmf (step s (qs!n) a,nis)) ) 
                 in
        E( map_pmf (phi (Suc n)) nextconfig) )"

lemma PhiPlus_is_Phi_Suc: "n<length qs \<Longrightarrow> PhiPlus n = Phi (Suc n)"
unfolding PhiPlus_def Phi_def 
apply (simp add: bind_return_pmf map_pmf_def bind_assoc_pmf split_def take_Suc_conv_app_nth )
  apply(simp add: config'_rand_snoc)
  by(simp add: bind_assoc_pmf split_def bind_return_pmf)

lemma phi0: "Phi 0 = 0" unfolding Phi_def 
   by (simp add: bind_return_pmf map_pmf_def bind_assoc_pmf BIT_init_def)

lemma phi_pos: "Phi n \<ge> 0"
  unfolding Phi_def
  apply(rule E_nonneg_fun)
  using phi_nonzero by auto
  
subsubsection "Helper lemmas"
lemma swap_subs: "dist_perm X Y \<Longrightarrow> Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}"
proof -
  assume "dist_perm X Y"
  note aj = Inv_swap[OF this, of z]                
  show "Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}"
  proof cases
    assume c1: "Suc z < length X"
    show "Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}"
    proof cases
      assume "Y ! z < Y ! Suc z in X"
      with c1 have "Inv X (swap z Y) = Inv X Y \<union> {(Y ! z, Y ! Suc z)}" using aj by auto
      then show "Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}" by auto
    next
      assume "~ Y ! z < Y ! Suc z in X"
      with c1 have "Inv X (swap z Y) = Inv X Y - {(Y ! Suc z, Y ! z)}" using aj by auto
      then show "Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}" by auto
    qed
  next
    assume "~ (Suc z < length X)"
    then have "Inv X (swap z Y) = Inv X Y" using aj by auto
    then show "Inv X (swap z Y) \<subseteq> Inv X Y \<union> {(Y ! z, Y ! Suc z)}" by auto
  qed
qed

 
subsubsection "InvOf"

term "Inv"      (*    BIT A *)
abbreviation "InvOf y bits as \<equiv> {(x,y)|x. x < y in bits \<and> y < x in as}"

lemma "InvOf y xs ys = {(x,y)|x. (x,y)\<in>Inv xs ys}"
unfolding Inv_def by auto

lemma "InvOf y xs ys \<subseteq> Inv xs ys" unfolding Inv_def by auto

lemma numberofIsbeschr: assumes
    distxsys: "dist_perm xs ys" and
    yinxs: "y \<in> set xs"
  shows "index xs y \<le> index ys y + card (InvOf y xs ys)" 
    (is "?iBit \<le> ?iA + card ?I")
proof -
  from assms have distinctxs: "distinct xs" 
      and distinctys: "distinct ys"
      and yinys: "y \<in> set ys" by auto

  let ?A="fst ` ?I"
  have aha: "card ?A = card ?I" apply(rule card_image)
    unfolding inj_on_def by(auto)
      
  have "?A \<subseteq> (before y xs)" by(auto)
  have "?A \<subseteq> (after y ys)" by auto



  have "finite (before y ys)" by auto

  have bef: "(before y xs) - ?A \<subseteq> before y ys" apply(auto)
  proof -
    fix x
    assume a: "x < y in xs"
    assume " x \<notin> fst ` {(x, y) |x. x < y in xs \<and> y < x in ys}"
    then have "~ (x < y in xs \<and> y < x in ys)" by force
    with a have d: "~ y < x in ys" by auto
    from a have "x \<in> set xs" by (rule before_in_setD1)
    with distxsys have b: "x \<in> set ys" by auto
    from a have  "y \<in> set xs" by (rule before_in_setD2)
    with distxsys have c: "y \<in> set ys" by auto
    from a have e: "~ x = y" unfolding before_in_def by auto 
    have "(\<not> y < x in ys) = (x < y in ys \<or> y = x)" apply(rule not_before_in)
      using b c by auto
    with d e show "x < y in ys" by auto
  qed
 
  have "(index xs y) - card (InvOf y xs ys) = card (before y xs) - card ?A"
    by(simp only: aha card_before[OF distinctxs yinxs])
  also have "\<dots> = card ((before y xs) - ?A)"
    apply(rule card_Diff_subset[symmetric]) by auto
  also have "\<dots> \<le> card (before y ys)"
  apply(rule card_mono)
   apply(simp)
   apply(rule bef)
  done
  also have "\<dots> = (index ys y)" by(simp only: card_before[OF distinctys yinys])
  finally have "index xs y - card ?I \<le> index ys y" .
  then show "index xs y  \<le> index ys y + card ?I" by auto
qed
 

lemma "length init = 0 \<Longrightarrow> length xs = length init \<Longrightarrow> t xs q (mf, sws) = 1 + length sws"
unfolding t_def by(auto)


lemma integr_index: "integrable (measure_pmf (config'' (BIT_init, BIT_step) qs init n))
   (\<lambda>(s, is). real (Suc (index s (qs ! n))))"
    apply(rule measure_pmf.integrable_const_bound[where B="Suc (length init)"])
      apply(simp add: split_def) apply (metis (mono_tags) index_le_size AE_measure_pmf_iff config_rand_length)
      by (auto)
 

subsubsection "Upper Bound on the Cost of BIT"
 

lemma t_BIT_ub2: "(qs!n) \<notin> set init \<Longrightarrow> t_BIT n \<le> Suc(size init)"
apply(simp add: t_BIT_def t_def BIT_step_def)
apply(simp add: bind_return_pmf)
proof (goal_cases)
  case 1
  note qs=this
  let ?D =  "(config'' (BIT_init, BIT_step) qs init n)"

  have absch: "(\<forall>x\<in> set_pmf ?D. ((\<lambda>(s,is). real (Suc (index s (qs ! n)))) x) \<le> ((\<lambda>(is,s). Suc (length init)) x))"
  proof (rule ballI, goal_cases)
    case (1 x) 
    from 1 config_rand_length have f1: "length (fst x) = length init" by fastforce
    from 1 config_rand_set have 2: "set (fst x) = set init" by fastforce

    from qs 2 have "(qs!n) \<notin>  set (fst x)" by auto
    then show ?case using f1 by (simp add: split_def)
  qed      

  have "integrable (measure_pmf (config'' (BIT_init, BIT_step) qs init n))
     (\<lambda>(s, is). Suc (length init))" by(simp)

  have "E(bind_pmf ?D (\<lambda>(s, is). return_pmf (real (Suc (index s (qs ! n))))))
          = E(map_pmf (\<lambda>(s, is). real (Suc (index s (qs ! n)))) ?D)"
          by(simp add: split_def map_pmf_def)
  also have "\<dots> \<le> E(map_pmf (\<lambda>(s, is). Suc (length init)) ?D)"
              apply (rule E_mono3)
                apply(fact integr_index)
                apply(simp)
                using absch by auto
  also have "\<dots> = Suc (length init)"
          by(simp add: split_def)
   finally show ?case by(simp add: map_pmf_def bind_assoc_pmf bind_return_pmf split_def)
 qed

lemma t_BIT_ub: "(qs!n) \<in> set init \<Longrightarrow> t_BIT n \<le> size init"
apply(simp add: t_BIT_def t_def BIT_step_def)
apply(simp add: bind_return_pmf)
proof (goal_cases)
  case 1
  note qs=this 
  let ?D =  "(config'' (BIT_init, BIT_step) qs init n)"

  have absch: "(\<forall>x\<in> set_pmf ?D. ((\<lambda>(s, is). real (Suc (index s (qs ! n)))) x) \<le> ((\<lambda>(s, is). length init) x))"
  proof (rule ballI, goal_cases)
    case (1 x) 
    from 1 config_rand_length have f1: "length (fst x) = length init" by fastforce
    from 1 config_rand_set have 2: "set (fst x) = set init" by fastforce

    from qs 2 have "(qs!n) \<in> set (fst x)" by auto
    then have "(index (fst x) (qs ! n)) < length init" apply(rule index_less) using f1 by auto
    then show ?case by (simp add: split_def)
  qed      

  have "E(bind_pmf ?D (\<lambda>(s, is). return_pmf (real (Suc (index s (qs ! n))))))
          = E(map_pmf (\<lambda>(s, is). real (Suc (index s (qs ! n)))) ?D)"
          by(simp add: split_def map_pmf_def)
  also have "\<dots> \<le> E(map_pmf (\<lambda>(s, is). length init) ?D)"
              apply(rule E_mono3)
                apply(fact integr_index)
                apply(simp)              
                using absch by auto
  also have "\<dots> = length init"
          by(simp add: split_def)
   finally show ?case by(simp add: map_pmf_def bind_assoc_pmf bind_return_pmf split_def)
 qed 

lemma T_BIT_ub: "\<forall>i<n. qs!i \<in> set init \<Longrightarrow> T_BIT n \<le> n * size init"
proof(induction n)
  case 0 show ?case by(simp add: T_BIT_def)
next 
  case (Suc n) thus ?case   
    using t_BIT_ub[where n="n"] by (simp add: T_BIT_def) 
qed
 
 

subsubsection "Main Lemma"
 
                                         
 
lemma myub: "n < length qs \<Longrightarrow> t_BIT n + Phi(n + 1) - Phi n \<le> (7 / 4) * t_A n - 3/4"
proof - 
  assume nqs: "n < length qs"
  have "t_BIT n + Phi (n+1) - Phi n \<le> (7 / 4) * t_A n - 3/4"
  proof (cases "length init > 0")
    case False  
    show ?thesis 
    proof -
      from False have qsn: "(qs!n) \<notin> set init" by auto
      from False have l0: "length init = 0" by auto
      then have "length (swaps (paid_A ! n) (s_A n)) = 0" using length_s_A  by auto
  
      with l0 have 4: "t_A n = 1 + length (paid_A ! n)" unfolding t_A_def c_A_def p_A_def by(simp)
  
      have 1: "t_BIT n \<le> 1" using t_BIT_ub2[OF qsn] l0 by auto
    
      { fix m
      have "phi m = (\<lambda>(b,(a,i)). phi m (b,(a,i)))" by auto
      also have "\<dots> = (\<lambda>(b,(a,i)). 0)" by(simp only: phi_empty2[OF l0])
      finally have "phi m= (\<lambda>(b,(a,i)). 0)". 
      } note phinull=this
  
      have 2: "PhiPlus n = 0" unfolding PhiPlus_def apply(simp) apply(simp only: phinull)
      by (auto simp: split_def)
      have 3:"Phi n = 0" unfolding Phi_def apply(simp only: phinull)
      by (auto simp: split_def)
  
      have "t_A n \<ge> 1 \<Longrightarrow> 1 \<le> 7 / 4 *   (t_A n) - 3 / 4" by(simp)
      with 4 have 5: "1 \<le> 7 / 4 *   (t_A n) - 3 / 4" by auto
  
      from 1 2 3 have "t_BIT n + PhiPlus n - Phi n \<le> 1" by auto
      also from 5 have "\<dots> \<le>  7 / 4 *   (t_A n) - 3 / 4" by auto
      
      finally show ?thesis using PhiPlus_is_Phi_Suc nqs by auto
   qed
  next
    case True
    let ?l = "length init"
    from True obtain l' where lSuc: "?l = Suc l'" by (metis Suc_pred)

    have 31: "n < length paid_A" using nqs by auto
 

    define q where "q = qs!n"
    define D where [simp]: "D = (config'' (BIT_init, BIT_step) qs init n)"
    define cost where [simp]: "cost = (\<lambda>(s, is).(t s q (if (fst is) ! (index (snd is) q) then 0 else length s, [])))"
    define \<Phi>\<^sub>2 where [simp]: "\<Phi>\<^sub>2 = (\<lambda>(s, is). ((phi (Suc n)) (step s q (if (fst is) ! (index (snd is) q) then 0 else length s, []),(flip (index (snd is) q) (fst is), snd is))))"
    define \<Phi>\<^sub>0 where [simp]: "\<Phi>\<^sub>0 = phi n"
           
    have inEreinziehn: "t_BIT n + Phi (n+1) - Phi n =  E (map_pmf (\<lambda>x. (cost x) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x)) D)"
    proof - 
      have "bind_pmf D
                      (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a,nis). return_pmf (real(t s (q) a))))
         = bind_pmf D
                      (\<lambda>(s, is). return_pmf (t s q (if (fst is) ! (index (snd is) q) then 0 else length s, [])))"
            unfolding BIT_step_def apply (auto simp: bind_return_pmf split_def)
              by (metis prod.collapse)
      also have "\<dots> = map_pmf cost D"  
                     by (auto simp: map_pmf_def split_def)
      finally have rightform1: "bind_pmf D
                      (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a,nis). return_pmf (real(t s (q) a))))
                      = map_pmf cost D" . 

      have rightform2: "map_pmf (phi (Suc n)) (bind_pmf D
          (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a, nis). return_pmf (step s (q) a, nis))))
            = map_pmf \<Phi>\<^sub>2 D" apply(simp add:  bind_return_pmf bind_assoc_pmf map_pmf_def split_def BIT_step_def)
            by (metis  prod.collapse)
      have "t_BIT n + Phi (n+1) - Phi n =
       t_BIT n + PhiPlus n - Phi n" using PhiPlus_is_Phi_Suc nqs by auto
      also have "\<dots> =
          T_on_rand_n BIT init qs n
         + E (map_pmf (phi (Suc n)) (bind_pmf D
            (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a, nis). return_pmf (step s (q) a, nis)))))
        - E (map_pmf (phi n) D)
        " unfolding  PhiPlus_def Phi_def  t_BIT_def q_def by auto
      also have "\<dots> = 
        E (bind_pmf D
                      (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a,nis). return_pmf (t s (q) a))))
        + E (map_pmf (phi (Suc n)) (bind_pmf D
            (\<lambda>(s, is). bind_pmf (BIT_step (s, is) (q)) (\<lambda>(a, nis). return_pmf (step s (q) a, nis)))))
        - E (map_pmf \<Phi>\<^sub>0 D)"  by (auto simp: q_def split_def)
      also have "\<dots> = E (map_pmf cost D)
                  + E (map_pmf \<Phi>\<^sub>2 D)
                  - E (map_pmf \<Phi>\<^sub>0 D)" using rightform1 rightform2 split_def by auto
      also have "\<dots> =  E (map_pmf (\<lambda>x. (cost x) + (\<Phi>\<^sub>2 x)) D) -  E (map_pmf (\<lambda>x. (\<Phi>\<^sub>0 x)) D)"
            unfolding D_def using E_linear_plus2[OF finite_config_BIT[OF dist_init]] by auto
      also have "\<dots> =  E (map_pmf (\<lambda>x. (cost x) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x)) D)"
            unfolding D_def by(simp only: E_linear_diff2[OF finite_config_BIT[OF dist_init]] split_def)
      finally show "t_BIT n + Phi (n+1) - Phi n 
            =  E (map_pmf (\<lambda>x. (cost x) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x)) D)" by auto
    qed 

    define xs where [simp]: "xs = s_A n"
    define xs' where [simp]: "xs' = swaps (paid_A!n) xs"
    define xs'' where [simp]: "xs'' = mtf2 (free_A!n) (q) xs'"
    define k where [simp]: "k = index xs' q"    (* position of the requested element in A's list *)
    define k' where [simp]: "k' = max 0 (k-free_A!n)" (* position where A moves the requested element to *)

    have [simp]: "length xs = length init" by auto

    have dp_xs_init[simp]: "dist_perm xs init" by auto
  

text "The Transformation"
 
    have ub_cost: "\<forall>x\<in>set_pmf D. (real (cost x)) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x) \<le> k + 1 + 
            (if (q) \<in> set init
              then (if (fst (snd x))!(index init q) then k-k' 
                                      else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1)))
              else 0)
              + (\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2 else 1))"
    proof (rule, goal_cases)
      case (1 x)
      note xinD=1 
      then have [simp]: "snd (snd x) = init" using D_def config_n_init3 by fast

      define b where "b = fst (snd x)"
      define ys where "ys = fst x"
      define aBIT where [simp]: "aBIT = (if b ! (index (snd (snd x)) q) then 0 else length ys, ([]::nat list))"
      define ys' where "ys' = step ys (q) aBIT"
      define b' where "b' = flip (index init q) b"
      define \<Phi>\<^sub>1 where "\<Phi>\<^sub>1 = (\<lambda>z:: 'a list\<times> (bool list \<times> 'a list) . (\<Sum>(x,y)\<in>(Inv ys xs'). (if fst (snd z)!(index init y) then 2::real else 1)))"

      have xs''_step: "xs'' = step xs (q) (free_A!n,paid_A!n)"
      unfolding xs'_def xs''_def xs_def step_def free_A_def paid_A_def
      by(auto simp: split_def)

      have gis2: "(\<Phi>\<^sub>2 (ys,(b,init))) = (\<Sum>(x,y)\<in>(Inv ys' xs''). (if b'!(index init y) then 2 else 1))" 
        apply(simp only: split_def)
        apply(simp only: xs''_step)
        apply(simp only: \<Phi>\<^sub>2_def phi.simps)
        unfolding b'_def b_def ys'_def aBIT_def q_def
        unfolding s_A.simps apply(simp only: split_def) by auto
      then have gis: "\<Phi>\<^sub>2 x = (\<Sum>(x,y)\<in>(Inv ys' xs''). (if b'!(index init y) then 2 else 1))"
        unfolding ys_def b_def by (auto simp: split_def)

      have his2: "(\<Phi>\<^sub>0 (ys,(b,init))) = (\<Sum>(x,y)\<in>(Inv ys xs). (if b!(index init y) then 2 else 1))"
        apply(simp only: split_def)
        apply(simp only: \<Phi>\<^sub>0_def phi.simps) by(simp add: split_def)
      then have his: "(\<Phi>\<^sub>0 x) = (\<Sum>(x,y)\<in>(Inv ys xs). (if b!(index init y) then 2 else 1))"  
        by(auto simp: ys_def b_def split_def phi')
          
      have dis: "\<Phi>\<^sub>1 x = (\<Sum>(x,y)\<in>(Inv ys xs'). (if b!(index init y) then 2 else 1))"
        unfolding \<Phi>\<^sub>1_def b_def by auto
  
      have "ys' = mtf2 (fst aBIT) (q) ys" by (simp add: step_def ys'_def) 

      from config_rand_distinct[of BIT] config_rand_set[of BIT] xinD
      have dp_ys_init[simp]: "dist_perm ys init" unfolding D_def ys_def by force
      have dp_ys'_init[simp]: "dist_perm ys' init" unfolding ys'_def step_def by (auto)
      then have lenys'[simp]: "length ys' = length init" by (metis distinct_card)
      have dp_xs'_init[simp]: "dist_perm xs' init" by auto
      have gra: "dist_perm ys xs'" by auto

      have leninitb[simp]: "length b = length init" using b_def config_n_fst_init_length2 xinD[unfolded] by auto
      have leninitys[simp]: "length ys = length init" using dp_ys_init by (metis distinct_card)

      {fix m
        have "dist_perm ys (s'_A n m)" using dp_ys_init by auto
      } note dist=this
 
      text "Upper bound of the inversions created by paid exchanges of A"

      (* ============================================

          first we adress the paid exchanges 
          
          paid cost of A: p_A *)
     

      let ?paidUB="(\<Sum>i<(length (paid_A!n)). (if b!(gebub n i) then 2::real else 1))"

      have paid_ub: "\<Phi>\<^sub>1 x \<le> \<Phi>\<^sub>0 x + ?paidUB"
      proof -
      
        have a: "length (paid_A ! n) \<le> length (paid_A ! n)" by auto
        have b: "xs' = (s'_A n (length (paid_A ! n)))" using s'A_m by auto
 
        {
          fix m
          have "m\<le>length (paid_A!n) \<Longrightarrow> (\<Sum>(x,y)\<in>(Inv ys (s'_A n m)). (if b!(index init y) then 2::real else 1)) \<le> (\<Sum>(x,y)\<in>(Inv ys xs). (if b!(index init y) then 2 else 1))
                              + (\<Sum>i<m. (if b!(gebub n i) then 2 else 1))"
        proof (induct m)
          case (Suc m)
          then have m_bd2: "m \<le> length (paid_A ! n)"
                and m_bd: "m < length (paid_A ! n)" by auto
          note yeah = Suc(1)[OF m_bd2]  

          let ?revm="(length (paid_A ! n) - Suc m)"
          note ah=Inv_swap[of "ys" "(s'_A n m)" "(paid_A ! n ! ?revm)", OF dist]
          have "(\<Sum>(xa, y)\<in>Inv ys (s'_A n (Suc m)). if b ! (index init y) then 2::real else 1)
              = (\<Sum>(xa, y)\<in>Inv ys (swap (paid_A ! n ! ?revm) (s'_A n m)). if b ! (index init y) then 2 else 1)" using s'_A.simps(2) by auto
          also
          have "\<dots> = (\<Sum>(xa, y)\<in>(if Suc (paid_A ! n ! ?revm) < length ys
   then if s'_A n m ! (paid_A ! n ! ?revm) < s'_A n m ! Suc (paid_A ! n ! ?revm) in ys
        then Inv ys (s'_A n m) \<union> {(s'_A n m ! (paid_A ! n ! ?revm), s'_A n m ! Suc (paid_A ! n ! ?revm))}
        else Inv ys (s'_A n m) - {(s'_A n m ! Suc (paid_A ! n ! ?revm), s'_A n m ! (paid_A ! n ! ?revm))}
   else Inv ys (s'_A n m)). if b ! (index init y) then 2::real else 1)" by (simp only: ah)
          also
          have "\<dots> \<le> (\<Sum>(xa, y)\<in>Inv ys (s'_A n m). if b ! (index init y) then 2::real else 1)
                        + (if (b) ! (index init (s'_A n m ! Suc (paid_A ! n ! ?revm))) then 2::real else 1)" (is "?A \<le> ?B")
               proof(cases "Suc (paid_A ! n ! ?revm) < length ys")
                case False (* FIXME! can't occur! because it has already been filtered out! see:
                 then have "False" using paidAnm_inbound apply(auto) using m_bd nqs by blast *)
                then have "?A = (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)" by auto
                also have "\<dots> \<le> (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1) +
                        (if b ! (index init (s'_A n m ! Suc (paid_A ! n ! ?revm))) then 2::real else 1)" by auto
                finally show "?A \<le> ?B" .
               next
                case True
                then have "?A = (\<Sum>(xa, y)\<in>(if s'_A n m ! (paid_A ! n ! ?revm) < s'_A n m ! Suc (paid_A ! n ! ?revm) in ys
                      then Inv ys (s'_A n m) \<union> {(s'_A n m ! (paid_A ! n ! ?revm), s'_A n m ! Suc (paid_A ! n ! ?revm))}
                      else Inv ys (s'_A n m) - {(s'_A n m ! Suc (paid_A ! n ! ?revm), s'_A n m ! (paid_A ! n ! ?revm))}
                        ). if b ! (index init y) then 2 else 1)" by auto
                also have "\<dots> \<le> ?B" (is "?A' \<le> ?B")
                proof (cases "s'_A n m ! (paid_A ! n ! ?revm) < s'_A n m ! Suc (paid_A ! n ! ?revm) in ys")
                  case True
                  let ?neurein="(s'_A n m ! (paid_A ! n ! ?revm), s'_A n m ! Suc (paid_A ! n ! ?revm))"
                  from True have "?A' = (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m) \<union> {?neurein}
                      ). if b ! (index init y) then 2 else 1)" by auto
                  also have "\<dots> = (\<Sum>(xa, y)\<in>insert ?neurein (Inv ys (s'_A n m)
                      ). if b ! (index init y) then 2 else 1)" by auto
                  also have "\<dots> \<le> (if b ! (index init (snd ?neurein)) then 2 else 1) 
                            + (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)"
                  proof (cases "?neurein \<in> Inv ys (s'_A n m)")
                    case True
                    then have "insert ?neurein (Inv ys (s'_A n m)) = (Inv ys (s'_A n m))" by auto
                    then have "(\<Sum>(xa, y)\<in>insert ?neurein (Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)
                        = (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)" by auto
                    also have "\<dots> \<le> (if b ! (index init (snd ?neurein)) then 2::real else 1) 
                            + (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)" by auto
                    finally show ?thesis .
                  next
                    case False
                    have "(\<Sum>(xa, y)\<in>insert ?neurein (Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)
                        = (\<Sum>y\<in>insert ?neurein (Inv ys (s'_A n m)). (\<lambda>i. if b ! (index init (snd i)) then 2 else 1) y)" by(auto simp: split_def)
                    also have "\<dots> = (\<lambda>i. if b ! (index init (snd i)) then 2 else 1) ?neurein
                            + (\<Sum>y\<in>(Inv ys (s'_A n m)) - {?neurein}. (\<lambda>i. if b ! (index init (snd i)) then 2 else 1) y)"
                            apply(rule sum.insert_remove) by(auto)
                    also have "\<dots> = (if b ! (index init (snd ?neurein)) then 2 else 1) 
                            + (\<Sum>y\<in>(Inv ys (s'_A n m)). (\<lambda>i. if b ! (index init (snd i)) then 2::real else 1) y)" using False by auto
                    also have "\<dots> \<le> (if b ! (index init (snd ?neurein)) then 2 else 1) 
                            + (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)" by(simp only: split_def)
                    finally show ?thesis .
                  qed                  
                  also have "\<dots> = (\<Sum>(xa, y)\<in>Inv ys (s'_A n m). if b ! (index init y) then 2 else 1) +
                        (if b ! (index init (s'_A n m ! Suc (paid_A ! n ! ?revm))) then 2 else 1)" by auto
                  finally show ?thesis .
                next
                  case False
                  then have "?A' = (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m) - {(s'_A n m ! Suc (paid_A ! n ! ?revm), s'_A n m ! (paid_A ! n ! ?revm))}
                        ). if b ! (index init y) then 2 else 1)" by auto
                  also have "\<dots> \<le> (\<Sum>(xa, y)\<in>(Inv ys (s'_A n m)). if b ! (index init y) then 2 else 1)" (is "(\<Sum>(xa, y)\<in>?X-{?x}. ?g y) \<le> (\<Sum>(xa, y)\<in>?X. ?g y) ")
                  proof (cases "?x \<in> ?X")                  
                    case True
                    have "(\<Sum>(xa, y)\<in>?X-{?x}. ?g y) \<le> (%(xa,y). ?g y) ?x + (\<Sum>(xa, y)\<in>?X-{?x}. ?g y)"
                       by simp
                    also have "\<dots> = (\<Sum>(xa, y)\<in>?X. ?g y)"
                      apply(rule sum.remove[symmetric])
                        apply simp apply(fact) done
                    finally show ?thesis .
                  qed simp 
                  also have "\<dots> \<le> ?B" by auto
                  finally show ?thesis .
                qed                   
                finally show "?A \<le> ?B" .
              qed 

          also have "\<dots> 
              \<le> (\<Sum>(xa, y)\<in>Inv ys (s_A n). if b ! (index init y) then 2::real else 1) + (\<Sum>i<m. if b ! gebub n i then 2::real else 1)
                        + (if (b) ! (index init (s'_A n m ! Suc (paid_A ! n ! ?revm))) then 2::real else 1)" using yeah by simp
          also have "\<dots> = (\<Sum>(xa, y)\<in>Inv ys (s_A n). if b ! (index init y) then 2::real else 1) + (\<Sum>i<m. if b ! gebub n i then 2 else 1)
                        + (if (b) ! gebub n m then 2 else 1)" unfolding gebub_def by simp
          also have "\<dots> = (\<Sum>(xa, y)\<in>Inv ys (s_A n). if b ! (index init y) then 2::real else 1) + (\<Sum>i<(Suc m). if b ! gebub n i then 2 else 1)"
                        by auto 
          finally show ?case by simp
        qed (simp add: split_def) 
        } note x = this[OF a]

        show ?thesis
          unfolding \<Phi>\<^sub>1_def his apply(simp only: b) using x b_def by auto
      qed

      text "Upper bound for the costs of BIT"

      define inI where [simp]: "inI = InvOf (q) ys xs'"
      define I where [simp]: "I = card(InvOf (q) ys xs')" 
            (* ys is BITs list, xs' is A's list after paid exchanges *)

      have ub_cost_BIT:  "(cost x) \<le> k + 1 + I"
      proof (cases "(q) \<in> set init")
        case False (* cannot occur! ! ! OBSOLETE *)
        from False have 4: "I = 0" by(auto simp: before_in_def)
        have "(cost x) = 1 + index ys (q)" by (auto simp: ys_def t_def split_def)
        also have "\<dots> = 1 + length init" using False by auto
        also have "\<dots> = 1 + k" using False by auto
        finally show ?thesis using 4 by auto
      next 
        case True
        then have gra2: "(q) \<in> set ys" using dp_ys_init by auto
        have "(cost x) = 1 + index ys (q)" by(auto simp:  ys_def t_def split_def)
        also have "\<dots> \<le> k + 1 + I" using numberofIsbeschr[OF gra gra2] by auto
        finally show"(cost x) \<le> k + 1 + I" . 
      qed

      text "Upper bound for inversions generated by free exchanges"

  (* ================================================ *)
      (* ================================================ *)

      (* second part: FREE EXCHANGES *)
 
      define ub_free
        where "ub_free =
          (if (q \<in> set init)
           then (if b!(index init q) then  k-k' else (\<Sum>j<k'. (if (b)!(index init (xs'!j)) then 2::real else 1) ))
           else 0)"
      let ?ub2 = "- I + ub_free"
      have free_ub: "(\<Sum>(x,y)\<in>(Inv ys' xs''). (if b' !(index init y) then 2 else 1 ) )
                - (\<Sum>(x,y)\<in>(Inv ys xs'). (if b!(index init y) then 2 else 1) ) \<le> ?ub2"
      proof (cases "(q) \<in> set init")
        case False

        from False have 1: "ys' = ys" unfolding ys'_def step_def mtf2_def by(simp)
        from False have 2: "xs' = xs''" unfolding xs''_def mtf2_def by(simp)
        from False have "(index init q) \<ge> length b" using setinit by auto
        then have 3: "b' = b" unfolding b'_def using flip_out_of_bounds by auto

        from False have 4: "I = 0" unfolding I_def before_in_def by(auto)
 
        note ubnn=False

        have nn: "k-k'\<ge>0" unfolding k_def k'_def by auto
          
        from 1 2 3 4 have "(\<Sum>(x,y)\<in>(Inv ys' xs''). (if b'!(index init y) then 2::real else 1))
                - (\<Sum>(x,y)\<in>(Inv ys xs'). (if b!(index init y) then 2 else 1)) = -I"  by auto
        with ubnn show ?thesis unfolding ub_free_def by auto
      next
        case True 
        note queryinlist=this


        then have gra2: "q \<in> set ys" using dp_ys_init by auto

        have k_inbounds: "k < length init" 
            using index_less_size_conv  queryinlist
              by (simp)
      {
          fix y  e
          fix X::"bool list"
          assume rd: "e < length X"
        have "y < length X \<Longrightarrow> (if flip e X ! y then 2::real else 1) - (if X ! y then 2 else 1)
              = (if e=y then (if X ! y then -1 else 1) else 0)"
          proof cases
             assume "y < length X" and ey: "e=y"
             then have "(if flip e X ! y then 2::real else 1) - (if X ! y then 2 else 1)
                      = (if X ! y then 1::real else 2) - (if X ! y then 2 else 1)" using flip_itself by auto
             also have "\<dots> = (if X ! y then -1::real else 1)" by auto
             finally
             show "(if flip e X ! y then 2::real else 1) - (if X ! y then 2 else 1)
              = (if e=y then (if X ! y then -1 else 1) else 0)" using ey by auto
          next
             assume len: "y < length X" and eny: "e\<noteq>y"
             then have "(if flip e X ! y then 2::real else 1) - (if X ! y then 2 else 1)
                      = (if X ! y then 2::real else 1) - (if X ! y then 2 else 1)" using flip_other[OF len rd eny]  by auto
             also have "\<dots> = 0" by auto
             finally
             show "(if flip e X ! y then 2::real else 1) - (if X ! y then 2 else 1)
              = (if e=y then (if X ! y then -1 else 1) else 0)" using eny by auto
          qed
       } note flipstyle=this
      
      from queryinlist setinit have qsfst: "(index init q) < length b" by simp

      have fA: "finite (Inv ys' xs'')" by auto
      have fB: "finite (Inv ys xs')" by auto


      define \<Delta> where [simp]: "\<Delta> = (\<Sum>(x,y)\<in>(Inv ys' xs''). (if b'!(index init y) then 2::real else 1))
                - (\<Sum>(x,y)\<in>(Inv ys xs'). (if b!(index init y) then 2 else 1))"
      define C where [simp]: "C = (\<Sum>(x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys xs'). (if b'!(index init y) then 2::real else 1)
                        - (if b!(index init y) then 2 else 1))"
      define A where [simp]: "A = (\<Sum>(x,y)\<in>(Inv ys' xs'')-(Inv ys xs'). (if b'!(index init y) then 2::real else 1))"
      define B where [simp]: "B = (\<Sum>(x,y)\<in>(Inv ys xs')-(Inv ys' xs''). (if b!(index init y) then 2::real else 1))"
        have teilen: "\<Delta> = C + A - B"  (* C A B *)
              unfolding \<Delta>_def A_def B_def C_def
                     using sum_my[OF fA fB]  by (auto simp: split_def)
        then have "\<Delta> = A - B + C" by auto  
        then have teilen2: "\<Phi>\<^sub>2 x - \<Phi>\<^sub>1 x  = A - B + C" unfolding \<Delta>_def using dis gis by auto
 
             
        have setys': "(index init) ` (set ys') = {0..<length ys'}"
          proof -
            have "(index init) ` (set ys') = (index init) ` (set init)" by auto
            also have "\<dots> = {0..<length init}" using setinit by auto
            also have "\<dots> = {0..<length ys'}" using lenys' by auto
            finally show ?thesis .
          qed
 
        have BC_absch: "C - B \<le> -I"

        proof (cases "b!(index init q)")    (* case distinction on whether the bit of the requested element is set *)
          case True
          then have samesame: "ys' = ys" unfolding ys'_def step_def by auto
          then have puh: "(Inv ys' xs') = (Inv ys xs')" by auto

          {
             fix \<alpha> \<beta>
             assume "(\<alpha>,\<beta>)\<in>(Inv ys' xs'') \<inter> (Inv ys' xs')"
             then have "(\<alpha>,\<beta>)\<in>(Inv ys' xs'')" by auto
             then have "(\<alpha>< \<beta> in ys')" unfolding Inv_def by auto
             then have 1: "\<beta> \<in> set ys'" by (simp only: before_in_setD2)
             then have  "index init \<beta> < length ys'" using setys' by auto
             then have  "index init \<beta> < length init" using lenys' by auto
             then have puzzel: "index init \<beta> < length b" using leninitb by auto


             have betainit: "\<beta> \<in> set init" using 1 by auto
             have aha: "(q=\<beta>) = (index init q = index init \<beta>)"
                using betainit by simp

             have "(if b'!(index init \<beta>) then 2::real else 1) - (if b!(index init \<beta>) then 2 else 1)
                = (if (index init q) = (index init \<beta>) then if b !(index init \<beta>) then - 1 else 1 else 0)" 
                  unfolding b'_def apply(rule flipstyle) by(fact)+
             also have "\<dots> = (if (index init q) = (index init \<beta>) then if b ! (index init q) then - 1 else 1 else 0)" by auto
             also have "\<dots> = (if q = \<beta> then - 1 else 0)" using aha True by auto
             finally have "(if b'!(index init \<beta>) then 2::real else 1) - (if b!(index init \<beta>) then 2 else 1)
                = (if (q) = \<beta> then -1::real else 0)" by auto
          }
          then have grreeeaa: "\<forall>x\<in>(Inv ys' xs'') \<inter> (Inv ys' xs').
              (\<lambda>x. (if b'! (index init (snd x)) then 2::real else 1) - (if b! (index init (snd x)) then 2 else 1)) x
                = (\<lambda>x. (if (q) = snd x then -1::real else 0)) x" by force

          let ?fin="(Inv ys' xs'') \<inter> (Inv ys' xs')"

          have ttt: "{(x,y). (x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys' xs')
                          \<and> y = (q)} \<union> {(x,y). (x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys' xs')
                          \<and> y \<noteq> (q)} = (Inv ys' xs'') \<inter> (Inv ys' xs')" (is "?split1 \<union> ?split2 = ?easy")  by auto
          have interem: "?split1 \<inter> ?split2 = {}" by auto
          have split1subs: "?split1 \<subseteq> ?fin" by auto
          have split2subs: "?split2 \<subseteq> ?fin" by auto
          have fs1: "finite ?split1" apply(rule finite_subset[where B="?fin"])
            apply(rule split1subs) by(auto)
          have fs2: "finite ?split2"  apply(rule finite_subset[where B="?fin"])
            apply(rule split2subs) by(auto)  
  
          have "k - k' \<le> (free_A!n)" by auto

          have g: "InvOf (q) ys' xs'' \<supseteq> InvOf (q) ys' xs'"
            using True apply(auto) apply(rule mtf2_mono[of "swaps (paid_A ! n) (s_A n)"])
              by (auto simp: queryinlist)
          have h: "?split1 = (InvOf (q) ys' xs'') \<inter> (InvOf (q) ys' xs')" 
            unfolding Inv_def by auto
          also from g have "\<dots> = InvOf (q) ys' xs'" by force
          also from samesame have "\<dots> = InvOf (q) ys  xs'" by simp
          finally have "?split1 = inI" unfolding inI_def .
          then have cardsp1isI: "card ?split1 = I" by auto
          
          {
            fix a b
            assume "(a,b)\<in>?split1"
            then have "b = (q)" by auto
            then have "(if (q) = b then (-1::real) else 0) = (-1::real)" by auto
          }  
          then have split1easy: "\<forall>x\<in>?split1.
              (\<lambda>x. (if (q) = snd x then (-1::real) else 0)) x = (\<lambda>x. (-1::real)) x" by force
          {
            fix a b
            assume "(a,b)\<in>?split2"
            then have "~ b = (q)" by auto
            then have "(if (q) = b then (-1::real) else 0) = 0" by auto
          }
          then have split2easy: "\<forall>x\<in>?split2.
              (\<lambda>x. (if (q) = snd x then (-1::real) else 0)) x = (\<lambda>x. 0::real) x" by force

                
          have E0: "C =
              (\<Sum>(x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys xs'). 
                      (if b'!(index init y) then 2::real else 1) - (if b!(index init y) then 2 else 1))" by auto
          also from puh have E1: "... =
              (\<Sum>(x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys' xs'). 
                      (if b'!(index init y) then 2::real else 1) - (if b!(index init y) then 2 else 1))" by auto
          also have E2: "\<dots> = (\<Sum>(x,y)\<in>?easy. 
                      (if (q) = y then (-1::real) else 0))" using sum_my2[OF grreeeaa] by (auto simp: split_def)
          also have E3: "\<dots> = (\<Sum>(x,y)\<in>?split1 \<union> ?split2. 
                      (if (q) = y then (-1::real) else 0))" by(simp only: ttt)
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if (q) = y then (-1::real) else 0))
                    + (\<Sum>(x,y)\<in>?split2. (if (q) = y then (-1::real) else 0))
                    - (\<Sum>(x,y)\<in>?split1 \<inter> ?split2. (if (q) = y then (-1::real) else 0))"
                    by(rule sum_Un[OF fs1 fs2]) 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if (q) = y then (-1::real) else 0))
                    + (\<Sum>(x,y)\<in>?split2. (if (q) = y then (-1::real) else 0))"
                    apply(simp only: interem) by auto
          also have E4: "\<dots> = (\<Sum>(x,y)\<in>?split1. (-1::real) )
                    + (\<Sum>(x,y)\<in>?split2. 0)"
                 using sum_my2[OF split1easy]sum_my2[OF split2easy] by(simp only: split_def)
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (-1::real) )" by auto
          also have E5: "\<dots> = - card ?split1 " by auto
          also have E6: "\<dots> = - I " using cardsp1isI by auto
          finally have abschC: "C = -I".

          have abschB: "B \<ge> (0::real)" unfolding B_def apply(rule sum_nonneg) by auto  
 
          from abschB abschC show "C - B \<le> -I" by simp

        next
          case False
          from leninitys False have ya: "ys' = mtf2 (length ys) q ys"
              unfolding step_def ys'_def by(auto)
          have "index ys' q = 0" 
            unfolding ya apply(rule mtf2_moves_to_front) 
            using gra2 by simp_all
          then have nixbefore: "before q ys' = {}" unfolding before_in_def by auto

          {
             fix \<alpha> \<beta>
             assume "(\<alpha>,\<beta>)\<in>(Inv ys' xs'') \<inter> (Inv ys xs')"
             then have "(\<alpha>,\<beta>)\<in>(Inv ys' xs'')" by auto
             then have "(\<alpha>< \<beta> in ys')" unfolding Inv_def by auto
             then have 1: "\<beta> \<in> set ys'" by (simp only: before_in_setD2)
             then have  "(index init \<beta>) < length ys'" using setys' by auto
             then have  "(index init \<beta>) < length init" using lenys' by auto
             then have puzzel: "(index init \<beta>) < length b" using leninitb by auto


             have betainit: "\<beta> \<in> set init" using 1 by auto 
             have aha: "(q=\<beta>) = (index init q = index init \<beta>)"
                using betainit by simp 

             have "(if b'!(index init \<beta>) then 2::real else 1) - (if b!(index init \<beta>) then 2 else 1)
                = (if (index init q) = (index init \<beta>) then if b ! (index init \<beta>) then - 1 else 1 else 0)" 
                  unfolding b'_def apply(rule flipstyle) by(fact)+
             also have "\<dots> = (if (index init q) = (index init \<beta>) then if b ! (index init q) then - 1 else 1 else 0)" by auto
             also have "\<dots> = (if (q) = \<beta> then 1 else 0)" using False aha by auto
             finally have "(if b'!(index init \<beta>) then 2::real else 1) - (if b!(index init \<beta>) then 2 else 1)
                = (if (q) = \<beta> then 1::real else 0)" by auto
          } 
          then have grreeeaa2: "\<forall>x\<in>(Inv ys' xs'') \<inter> (Inv ys xs').
              (\<lambda>x. (if b'! (index init (snd x)) then 2::real else 1) - (if b! (index init (snd x)) then 2 else 1)) x
                = (\<lambda>x. (if (q) = snd x then 1::real else 0)) x" by force

          let ?fin="(Inv ys' xs'') \<inter> (Inv ys xs')"

          have ttt: "{(x,y). (x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys  xs')
                          \<and> y = (q)} \<union> {(x,y). (x,y)\<in>(Inv ys' xs'') \<inter> (Inv ys  xs')
                          \<and> y \<noteq> (q)} = (Inv ys' xs'') \<inter> (Inv ys  xs')" (is "?split1 \<union> ?split2 = ?easy")  by auto
          have interem: "?split1 \<inter> ?split2 = {}" by auto
          have split1subs: "?split1 \<subseteq> ?fin" by auto
          have split2subs: "?split2 \<subseteq> ?fin" by auto
          have fs1: "finite ?split1" apply(rule finite_subset[where B="?fin"])
            apply(rule split1subs) by(auto)
          have fs2: "finite ?split2"  apply(rule finite_subset[where B="?fin"])
            apply(rule split2subs) by(auto)  
         
          have split1easy : "\<forall>x\<in>?split1.
              (\<lambda>x. (if (q) = snd x then (1::real) else 0)) x = (\<lambda>x. (1::real)) x" by force

          have split2easy : "\<forall>x\<in>?split2.
              (\<lambda>x. (if (q) = snd x then (1::real) else 0)) x = (\<lambda>x. (0::real)) x" by force



          from nixbefore have InvOfempty: "InvOf q ys' xs'' = {}" unfolding Inv_def by auto

          have "?split1 = InvOf q ys' xs'' \<inter> InvOf q ys xs'" 
              unfolding Inv_def by auto
          also from InvOfempty have "\<dots> = {}" by auto
          finally have split1empty: "?split1 = {}" .

          have "C  = (\<Sum>(x,y)\<in>?easy. 
                      (if (q) = y then (1::real) else 0))" unfolding C_def by(simp only: split_def sum_my2[OF grreeeaa2])
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1 \<union> ?split2. 
                      (if (q) = y then (1::real) else 0))" by(simp only: ttt)
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if (q) = y then (1::real) else 0))
                    + (\<Sum>(x,y)\<in>?split2. (if (q) = y then (1::real) else 0))
                    - (\<Sum>(x,y)\<in>?split1 \<inter> ?split2. (if (q) = y then (1::real) else 0))"
                    by(rule sum_Un[OF fs1 fs2]) 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if (q) = y then (1::real) else 0))
                    + (\<Sum>(x,y)\<in>?split2. (if (q) = y then (1::real) else 0))"
                    apply(simp only: interem) by auto 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (1::real) )
                    + (\<Sum>(x,y)\<in>?split2. 0)" using sum_my2[OF split1easy] sum_my2[OF split2easy] by (simp only: split_def) 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (1::real) )" by auto
          also have "\<dots> = card ?split1" by auto
          also have "\<dots> = (0::real)" apply(simp only: split1empty) by auto
          finally have abschC: "C = (0::real)" .
          
          (* approx for B *)

          have ttt2: "{(x,y). (x,y)\<in>(Inv ys  xs') - (Inv ys' xs'')
                          \<and> y = (q)} \<union> {(x,y). (x,y)\<in>(Inv ys  xs') - (Inv ys' xs'')
                          \<and> y \<noteq> (q)} = (Inv ys  xs') - (Inv ys' xs'')" (is "?split1 \<union> ?split2 = ?easy2")  by auto
          have interem: "?split1 \<inter> ?split2 = {}" by auto
          have split1subs: "?split1 \<subseteq> ?easy2" by auto
          have split2subs: "?split2 \<subseteq> ?easy2" by auto
          have fs1: "finite ?split1" apply(rule finite_subset[where B="?easy2"])
            apply(rule split1subs) by(auto)
          have fs2: "finite ?split2"  apply(rule finite_subset[where B="?easy2"])
            apply(rule split2subs) by(auto)  
             
          from False have split1easy2: "\<forall>x\<in>?split1.
              (\<lambda>x. (if b! (index init (snd x)) then 2::real else 1)) x = (\<lambda>x. (1::real)) x" by force

          have "?split1 = (InvOf q ys  xs') - (InvOf q ys' xs'')" 
              unfolding Inv_def by auto
          also have "\<dots> =  inI" unfolding InvOfempty by auto 
          finally have splI: "?split1 = inI" .

          have abschaway: "(\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1)) \<ge> 0"
              apply(rule sum_nonneg) by auto
          
         have "B  =  (\<Sum>(x,y)\<in>?split1 \<union> ?split2. 
                      (if b!(index init y) then 2::real else 1) )" unfolding B_def by(simp only: ttt2)
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if b!(index init y) then 2::real else 1))
                    + (\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1))
                    - (\<Sum>(x,y)\<in>?split1 \<inter> ?split2. (if b!(index init y) then 2::real else 1))"
                    by(rule sum_Un[OF fs1 fs2]) 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. (if b!(index init y) then 2::real else 1))
                    + (\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1))"
                    apply(simp only: interem) by auto 
          also have "\<dots> = (\<Sum>(x,y)\<in>?split1. 1)
                    + (\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1))"
                 using sum_my2[OF split1easy2] by (simp only: split_def)
          also have "\<dots> = card ?split1
                    + (\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1))" by auto
          also have "\<dots> = I
                    + (\<Sum>(x,y)\<in>?split2. (if b!(index init y) then 2::real else 1))" using splI by auto
          also have "\<dots> \<ge> I" using abschaway by auto
          finally have abschB: "B \<ge> I" .

          from abschB abschC show "C - B \<le> -I" by auto
        qed
 

        (* ==========================================
            central! calculations for A 
           ========================================== *)
 
        have A_absch: "A
              \<le> (if b!(index init q) then k-k' else (\<Sum>j<k'. (if b!(index init (xs'!j)) then 2::real else 1)))"
        proof (cases "b!(index init q)") (* case distinction on whether the requested element's bit is set *)
          case False
 
          from leninitys False have ya: "ys' = mtf2 (length ys) q ys" (* BIT moves q to front *)
              unfolding step_def ys'_def by(auto)
          have "index ys' q = 0" unfolding ya apply(rule mtf2_moves_to_front) 
             using gra2 by(simp_all)
          then have nixbefore: "before q ys' = {}" unfolding before_in_def by auto
          
          have "A = (\<Sum>(x,y)\<in>(Inv ys' xs'')-(Inv ys xs'). (if b'!(index init y) then 2::real else 1))" by auto
          

          have "index (mtf2 (free_A ! n) (q) (swaps (paid_A ! n) (s_A n))) (q)
              = (index (swaps (paid_A ! n) (s_A n)) (q) - free_A ! n)" 
                apply(rule mtf2_q_after) using queryinlist by auto
          then have whatisk': "k' = index xs'' q" by auto


          have ss: "set ys' = set ys" by auto
          have ss2: "set xs' = set xs''" by auto

          have di: "distinct init" by auto
          have dys: "distinct ys" by auto

          have "(Inv ys' xs'')-(Inv ys xs')
              = {(x,y). x < y in ys' \<and> y < x in xs'' \<and> (~x < y in ys \<or> ~ y < x in xs')}"
              unfolding Inv_def by auto 
          also have "\<dots>  = 
            {(x,y). y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> (~x < y in ys \<or> ~ y < x in xs') }"
              using nixbefore by blast
          also have "\<dots>  = 
            {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> (~x < y in ys \<or> ~ y < x in xs') }"
              unfolding before_in_def by auto
          also have "\<dots>  = 
            {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> ~x < y in ys }
            \<union> {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and>  ~ y < x in xs' }"
              by force
          also have "\<dots>  = 
            {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> y < x in ys }
            \<union> {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and>  ~ y < x in xs' }"
              using  before_in_setD1[where xs="ys'"] before_in_setD2[where xs="ys'"] not_before_in ss by metis
          also have "\<dots>  = 
            {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> y < x in ys }
            \<union> {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and>  x < y in xs' }" (is "?S1 \<union> ?S2 = ?S1 \<union> ?S2'")
              proof -
                have "?S2 = ?S2'" apply(safe)
                proof (goal_cases)
                  case (2 a b)
                  from 2(5) have "~ b < a in xs'" by auto
                  with 2(6) show "False" by auto
                next
                  case (1 a b)
                  from 1(4) have "a \<in> set xs'" "b \<in> set xs'" 
                    using  before_in_setD1[where xs="xs''"]
                     before_in_setD2[where xs="xs''"] ss2 by auto
                  with not_before_in 1(5) have "(a < b in xs' \<or> a = b)" by metis
                  with 1(1) show "a < b in xs'" by auto
                qed
                then show ?thesis by auto
              qed
           also have "\<dots>  = 
            {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> y < x in ys }
            \<union> {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> ~ x < y in xs'' \<and>  x < y in xs' }" (is "?S1 \<union> ?S2 = ?S1 \<union> ?S2'")
              proof -
                have "?S2 = ?S2'" apply(safe)
                proof (goal_cases)
                  case (1 a b)
                  from 1(4) have "~ a < b in xs''" by auto
                  with 1(6) show "False" by auto
                next
                  case (2 a b)
                  from 2(5) have "a \<in> set xs''" "b \<in> set xs''" 
                    using  before_in_setD1[where xs="xs'"]
                     before_in_setD2[where xs="xs'"] ss2 by auto
                  with not_before_in 2(4) have "(b < a in xs'' \<or> a = b)" by metis
                  with 2(1) show "b < a in xs''" by auto
                qed
                then show ?thesis by auto
              qed
           also have "\<dots>  = 
              {(x,y). x\<noteq>y \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> y < x in ys }
              \<union> {}"
                using x_stays_before_y_if_y_not_moved_to_front[where xs="xs'" and q="q"] 
                    before_in_setD1[where xs="xs'"] before_in_setD2[where xs="xs'"]  by (auto simp: queryinlist) 
           also have "\<dots>  = 
              {(x,y). x\<noteq>y \<and> x=q \<and> y\<noteq>q \<and> x < y in ys' \<and> y < x in xs'' \<and> y < x in ys }"
                apply(simp only: ya) using swapped_by_mtf2[where xs="ys" and q="q" and n="(length ys)"]  dys
                  before_in_setD1[where xs="ys"] before_in_setD2[where xs="ys"] by (auto simp: queryinlist) 
          also have "\<dots>  \<subseteq> 
            {(x,y). x=q \<and> y\<noteq>q \<and> q < y in ys' \<and> y < q in xs''}" by force
          also have "\<dots> = 
            {(x,y). x=q \<and> y\<noteq>q \<and> q < y in ys' \<and> y < q in xs'' \<and> y \<in> set xs''}" 
              using before_in_setD1 by metis
          also have "\<dots>  = 
            {(x,y). x=q \<and> y\<noteq>q \<and> q < y in ys' \<and> index xs'' y < index xs'' q \<and> q \<in> set xs'' \<and> y \<in> set xs''}" unfolding before_in_def by auto 
          also have "\<dots>  = 
            {(x,y). x=q \<and> y\<noteq>q \<and> q < y in ys' \<and> index xs'' y < index xs' q - (free_A ! n) \<and> q \<in> set xs'' \<and> y \<in> set xs''}"
              using mtf2_q_after[where A="xs'" and q="q"] by force
          also have "\<dots>  \<subseteq> 
            {(x,y). x=q \<and> y\<noteq>q \<and> index xs' y < index xs' q - (free_A ! n) \<and> y \<in> set xs''}" 
              using mtf2_backwards_effect4'[where xs="xs'" and q="q" and n="(free_A ! n)", simplified ]
              by auto
          also have "\<dots> \<subseteq>
            {(x,y). x=q \<and> y\<noteq>q \<and> index xs' y < k'}" 
              using mtf2_q_after[where A="xs'" and q="q"] by auto

          finally have subsa: "(Inv ys' xs'')-(Inv ys xs')
              \<subseteq> {(x,y). x=q \<and> y\<noteq>q \<and> index xs' y < k'}" .
 
          have k'xs': "k' < length xs''" unfolding whatisk'
            apply(rule index_less) by (auto simp: queryinlist) 
          then have k'xs': "k' < length xs'" by auto

          have "{(x,y). x=q \<and> index xs' y < k'}
              \<subseteq> {(x,y). x=q  \<and> index xs' y < length xs'}" using k'xs' by auto
          also have "\<dots> = {(x,y). x=q \<and>  y \<in> set xs'}" 
              using index_less_size_conv by fast
          finally have "{(x,y). x=q \<and> index xs' y < k'} \<subseteq> {(x,y). x=q \<and> y \<in> set xs'}" .
          then have finia2: "finite {(x,y). x=q \<and> index xs' y < k'}"
            apply(rule finite_subset) by(simp)

          have lulae: "{(a,b). a=q \<and> index xs' b < k'}
              = {(q,b)|b.  index xs' b < k'}" by auto

          have k'b: "k' < length b" using whatisk' by (auto simp: queryinlist) 
          have asdasd: "{(\<alpha>,\<beta>). \<alpha>=q \<and> \<beta>\<noteq>q \<and> index xs' \<beta> < k'} 
            = {(\<alpha>,\<beta>). \<alpha>=q \<and> \<beta>\<noteq>q \<and> index xs' \<beta> < k' \<and>  (index init \<beta>) < length b }"
                    proof (auto, goal_cases)
                      case (1 b)
                      from 1(2) have "index xs' b < index xs' (q)" by auto
                      also have "\<dots> < length xs'" by (auto simp: queryinlist) 
                      finally have "b \<in> set xs'" using index_less_size_conv by metis
                      then show ?case using setinit by auto
                    qed
            
         { fix \<beta>
           have "\<beta>\<noteq>q \<Longrightarrow>  (index init \<beta>)\<noteq>(index init q)"
            using queryinlist by auto
         } note ij=this
         have subsa2: "{(\<alpha>,\<beta>). \<alpha>=q \<and> \<beta>\<noteq>q \<and> index xs' \<beta> < k'}  \<subseteq>
            {(\<alpha>,\<beta>). \<alpha>=q \<and> index xs' \<beta> < k'}" by auto
          then have finia: "finite {(x,y). x=q \<and> y\<noteq>q \<and> index xs' y < k'}"
            apply(rule finite_subset) using finia2 by auto

          have E0: "A = (\<Sum>(x,y)\<in>(Inv ys' xs'')-(Inv ys xs'). (if b'!(index init y) then 2::real else 1))" by auto
          also have E1: "\<dots> \<le> (\<Sum>(x,y)\<in>{(a,b). a=q \<and> b\<noteq>q \<and> index xs' b < k'}. (if b'!(index init y) then 2::real else 1))"
              unfolding A_def apply(rule sum_mono2[OF finia subsa]) by auto
          also have "\<dots> = (\<Sum>(x,y)\<in>{(\<alpha>,\<beta>). \<alpha>=q \<and> \<beta>\<noteq>q \<and> index xs' \<beta> < k'
                          \<and>   (index init \<beta>) < length b }. (if b'!(index init y) then 2::real else 1))"
                          using asdasd  by auto
          also have "\<dots> = (\<Sum>(x,y)\<in>{(\<alpha>,\<beta>). \<alpha>=q \<and> \<beta>\<noteq>q \<and> index xs' \<beta> < k' 
                          \<and>  (index init \<beta>) < length b }. (if b!(index init y) then 2::real else 1))"
          proof (rule sum.cong, goal_cases)
             case (2 z)
             then obtain \<alpha> \<beta> where zab: "z=(\<alpha>, \<beta>)" and "\<alpha> = q" and diff: "\<beta> \<noteq> q" and "index xs' \<beta> < k'" and i: "index init \<beta> < length b" by auto
             from diff ij have "index init \<beta> \<noteq> index init q" by auto
             with flip_other qsfst i have "b' ! index init \<beta> =  b ! index init \<beta>" unfolding b'_def  by auto
             with zab show ?case by(auto simp add:  split_def)
          qed simp
          also have E1a: "\<dots> = (\<Sum>(x,y)\<in>{(a,b). a=q \<and> b\<noteq>q \<and> index xs' b < k'}. (if b!(index init y) then 2::real else 1))"
                          using asdasd  by auto
          also have "\<dots> \<le> (\<Sum>(x,y)\<in>{(a,b). a=q \<and> index xs' b < k'}. (if b!(index init y) then 2::real else 1))"
              apply(rule sum_mono2[OF finia2 subsa2]) by auto
          also have E2: "\<dots> = (\<Sum>(x,y)\<in>{(q,b)|b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))" 
              by (simp only: lulae[symmetric])
          finally have aa: "A \<le> (\<Sum>(x,y)\<in>{(q,b)|b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))" .

          have sameset: "{y. index xs' y < k'} = {xs'!i | i. i < k'}" 
            proof (safe, goal_cases)
              case (1 z)
              show ?case
                proof 
                from 1(1) have "index xs' z < index (swaps (paid_A ! n) (s_A n)) (q)"
                  by auto
                also have "\<dots> < length xs'" using index_less_size_conv by (auto simp: queryinlist) 
                finally have "index xs' z  < length xs'" .
                then have zset: "z \<in> set xs'" using index_less_size_conv by metis
                have f1: "xs' ! (index xs' z) = z"
                  apply(rule nth_index) using zset by auto
                show "z = xs' ! (index xs' z) \<and> (index xs' z) < k'"
                using f1 1(1)  by auto
              qed
            next
              case (2 k i)
              from 2(1) have "i < index (swaps (paid_A ! n) (s_A n)) (q)"
                by auto
              also have "\<dots> < length xs'" using index_less_size_conv by (auto simp: queryinlist) 
              finally have iset: "i < length xs'" .
              have "index xs' (xs' ! i) = i" apply(rule index_nth_id)
                using iset by(auto)
              with 2 show ?case by auto
            qed
           
          have aaa23: "inj_on (\<lambda>i. xs'!i) {i. i < k'}"
            apply(rule inj_on_nth)
              apply(simp)
              apply(simp) proof (safe, goal_cases)
                case (1 i)
                then have "i < index xs' (q)" by auto
                also have "\<dots> < length xs'" using index_less_size_conv by (auto simp: queryinlist) 
                also have "\<dots> = length init" by auto
                finally show " i < length init" .
              qed


          have aa3: "{xs'!i | i. i < k'} = (\<lambda>i. xs'!i) ` {i. i < k'}" by auto
          have aa4: "{(q,b)|b. index xs' b < k'} = (\<lambda>b. (q,b)) ` {b. index xs' b < k'}" by auto
             

          have unbelievable: "{i::nat. i < k'} = {..<k'}" by auto

          have aadad: "inj_on (\<lambda>b. (q,b)) {b. index xs' b < k'}" 
            unfolding inj_on_def by(simp)

          have "(\<Sum>(x,y)\<in>{(q,b)|b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))
                = (\<Sum>y\<in>{y. index xs' y < k'}. (if b!(index init y) then 2::real else 1))"
                proof -
                  have "(\<Sum>(x,y)\<in>{(q,b)|b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))
                    = (\<Sum>(x,y)\<in> (\<lambda>b. (q,b)) ` {b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))" using aa4 by simp
                  also have "\<dots> = (\<Sum>z\<in> (\<lambda>b. (q,b)) ` {b. index xs' b < k'}. (if b!(index init (snd z)) then 2::real else 1))" by (simp add: split_def)
                  also have "\<dots> = (\<Sum>z\<in>{b. index xs' b < k'}. (if b!(index init (snd ((\<lambda>b. (q,b)) z))) then 2::real else 1))"
                      apply(simp only: sum.reindex[OF aadad]) by auto  
                  also have "\<dots> = (\<Sum>y\<in>{y. index xs' y < k'}. (if b!(index init y) then 2::real else 1))" by auto
                  finally show ?thesis .
                qed
          also have "\<dots> = (\<Sum>y\<in>{xs'!i | i. i < k'}. (if b!(index init y) then 2::real else 1))" using sameset by auto
          also have "\<dots> = (\<Sum>y\<in>(\<lambda>i. xs'!i) ` {i. i < k'}. (if b!(index init y) then 2::real else 1))" using aa3 by simp
          also have "\<dots> = (\<Sum>y\<in>{i::nat. i < k'}. (if b!(index init (xs'!y)) then 2::real else 1))" 
                using sum.reindex[OF aaa23] by simp
          also have E3: "\<dots> = (\<Sum>j::nat<k'. (if b!(index init (xs'!j)) then 2::real else 1))" 
                  using unbelievable by auto
          finally have bb: "(\<Sum>(x,y)\<in>{(q,b)|b. index xs' b < k'}. (if b!(index init y) then 2::real else 1))
              = (\<Sum>j<k'. (if b!(index init (xs'!j)) then 2::real else 1))" .
 
          have "A \<le> (\<Sum>j<k'. (if b!(index init (xs'!j)) then 2::real else 1))"
            using aa bb by linarith

     
          then show "A
              \<le> (if b!(index init q) then k-k' else (\<Sum>j<k'. (if b!(index init (xs'!j)) then 2::real else 1)))"
              using False by auto   

        next
          case True
 
          then have samesame: "ys' = ys" unfolding ys'_def step_def by auto (* BIT does nothing *)

          have setxsbleibt: "set xs'' = set init" by auto
  
          have whatisk': "k' = index xs'' q" apply(simp)
              apply(rule mtf2_q_after[symmetric]) using queryinlist  by auto
                
          have "(Inv ys' xs'')-(Inv ys xs')
              = {(x,y). x < y in ys  \<and> y < x in xs'' \<and>  ~ y < x in xs'}"
                    unfolding Inv_def using samesame by auto  
          also have 
            "\<dots> \<subseteq>  {(xs'!i,q)|i. i\<in>{k'..<k}}"
           apply(clarify)
           proof 
              fix a b
              assume 1: "a < b in ys"
                and 2: "b < a in xs''"
                and 3: "\<not> b < a in xs'"
              then have anb: "a \<noteq> b"
                  using no_before_inI by(force)
              have a: "a \<in> set init"
                  and b: "b \<in> set init"
                    using  before_in_setD1[OF 1] before_in_setD2[OF 1] by auto
              with anb 3 have 3: "a < b in xs'"                      
                      by (simp add: not_before_in) 
              note all= anb 1 2 3 a b 
              have bq: "b=q" apply(rule swapped_by_mtf2[where xs="xs'" and x=a])
               using queryinlist apply(simp_all add: all) 
               using all(4) apply(simp) 
               using all(3) apply(simp) done

              note mine=mtf2_backwards_effect3[THEN conjunct1]

              from bq have "q < a in xs''" using 2 by auto
              then have "(k' < index xs'' a \<and> a \<in> set xs'')"
                unfolding before_in_def
                  using  whatisk' by auto
              then have low : "k' \<le> index xs' a"
                unfolding whatisk'
                 unfolding xs''_def  
                 apply(subst mtf2_q_after)
                   apply(simp)
                  using queryinlist apply(simp) 
                 apply(rule mine)
                    apply (simp add: queryinlist)
                   using bq b apply(simp)
                  apply(simp)
                 apply(simp del: xs'_def)
                 apply (metis "3" a before_in_def bq dp_xs'_init k'_def k_def max_0L mtf2_forward_beforeq nth_index whatisk' xs''_def)
                using a by(simp)(* 

                 unfolding xs'_def xs_def
                sledgehammer TODO: make this step readable  
by (metis "3" mtf2_q_after a before_in_def bq dp_xs'_init index_less_size_conv mtf2_forward_beforeq nth_index whatisk' xs''_def xs'_def xs_def)
 *)
              from bq have "a < q in xs'" using 3 by auto
              then have up: "(index xs' a < k )"
                unfolding before_in_def by auto

              from a have "a \<in> set xs'" by simp
              then have aa: "a = xs'!index xs' a" using nth_index by simp 

              have inset: "index xs' a \<in> {k'..<k}"
                using low up by fastforce

              from bq aa show "(a, b) = (xs' ! index xs' a, q) \<and> index xs' a \<in> {k'..<k}"
                using inset by simp 
            qed 
          finally have a: "(Inv ys' xs'')-(Inv ys xs') \<subseteq> {(xs'!i,q)|i. i\<in>{k'..<k}}" (is "?M \<subseteq> ?UB") .
 
          have card_of_UB: "card {(xs'!i,q)|i. i\<in>{k'..<k}} = k-k'" 
          proof -
            have e: "fst ` ?UB = (%i. xs' ! i) ` {k'..<k}" by force
            have "card ?UB = card (fst ` ?UB)"
                  apply(rule card_image[symmetric])
                      using inj_on_def by fastforce
          also
            have "\<dots> = card ((%i. xs' ! i) ` {k'..<k})" 
              by (simp only: e)
          also
            have "\<dots> = card {k'..<k}"
                  apply(rule card_image)
                  apply(rule inj_on_nth)
                    using k_inbounds by simp_all 
          also
            have "\<dots> = k-k'" by auto
          finally
            show ?thesis .
          qed
 
          have flipit: "flip (index init q) b ! (index init q) =  (~ (b) ! (index init q))" apply(rule flip_itself)
            using queryinlist setinit by auto

           
          have q: "{x\<in>?UB. snd x=q} = ?UB" by auto

          have E0: "A = (\<Sum>(x,y)\<in>(Inv ys' xs'')-(Inv ys xs'). (if b'!(index init y) then 2::real else 1))" by auto
          also have E1: "\<dots> \<le> (\<Sum>(z,y)\<in>?UB. if flip (index init q) (b) ! (index init y) then 2::real else 1)" 
              unfolding b'_def apply(rule sum_mono2[OF _ a]) 
                by(simp_all add: split_def)
          also have "\<dots> = (\<Sum>(z,y)\<in>{x\<in>?UB. snd x=q}. if flip (index init q) (b) ! (index init y) then 2::real else 1)" by(simp only: q)
          also have "\<dots> = (\<Sum>z\<in>{x\<in>?UB. snd x=q}. if flip (index init q) (b) ! (index init (snd z)) then 2::real else 1)" by(simp add: split_def)
          also have "\<dots> = (\<Sum>z\<in>{x\<in>?UB. snd x=q}. if flip (index init q) (b) ! (index init q) then 2::real else 1)" by simp
          also have E2: "\<dots> = (\<Sum>z\<in>?UB. if flip (index init q) (b) ! (index init q) then 2::real else 1)" by(simp only: q)
          also have E3: "\<dots> = (\<Sum>y\<in>?UB. 1)" using flipit True by simp
          also have E4: "\<dots> = k-k'"
              by(simp only: real_of_card[symmetric] card_of_UB)  
          finally have result: "A \<le>  k-k'" .
          with True show ?thesis by auto
        qed


        show "(\<Sum>(x,y)\<in>(Inv ys' xs''). (if b'!(index init y) then 2::real else 1)) - (\<Sum>(x,y)\<in>(Inv ys xs'). (if b!(index init y) then 2::real else 1)) \<le> ?ub2" 
                  unfolding ub_free_def teilen[unfolded \<Delta>_def A_def B_def C_def] using BC_absch A_absch using True 
                    by auto
      qed 
      from paid_ub have kl: "\<Phi>\<^sub>1 x \<le> \<Phi>\<^sub>0 x + ?paidUB" by auto
      from free_ub have kl2: "\<Phi>\<^sub>2 x -  ?ub2 \<le> \<Phi>\<^sub>1 x" using gis dis by auto

 
      have iub_free: "I + ?ub2 =  ub_free" by auto 

      from kl kl2 have "\<Phi>\<^sub>2 x - \<Phi>\<^sub>0 x \<le> ?ub2 + ?paidUB" by auto

      then have "(cost x) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x) \<le> k + 1 + I + ?ub2 + ?paidUB" using ub_cost_BIT by auto
  
      then show ?case unfolding ub_free_def b_def by auto 
    qed   

text "Approximation of the Term for Free exchanges"

 
    have free_absch: "E(map_pmf (\<lambda>x. (if (q) \<in> set init then (if (fst (snd x))!(index init q) then k-k' 
                else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1))) else 0)) D)
          \<le> 3/4 * k" (is "?EA \<le> ?absche")
    proof (cases "(q) \<in> set init")
      case False
       
      then have "?EA = 0" by auto 
      then show ?thesis by auto
    next
      case True


      note queryinlist=this

      have "k-k' \<le> k" by auto
      have "k' \<le> k" by auto
 

      text "Transformation of the first term" 

 

        have qsn: "{index init q} \<union> {} \<subseteq> {0..<?l}" using setinit queryinlist by auto

        have "{l::bool list. length l = ?l \<and> l!(index init q)}
          = {xs. Ball {(index init q)} ((!) xs) \<and> (\<forall>i\<in>{}. \<not> xs ! i) \<and> length xs = ?l}" by auto
        then have "card {l::bool list. length l = ?l \<and> l!(index init q)}
          = card {xs. Ball {index init q} ((!) xs) \<and> (\<forall>i\<in>{}. \<not> xs ! i) \<and> length xs = length init} " by auto
        also have "\<dots> = 2^(length init - card {index init q} - card {})" 
                  apply(subst card2[of "{(index init q)}" "{}" "?l"]) using qsn by auto
        finally have lulu: "card {l::bool list. length l = ?l \<and> l!(index init q)} = 2^(?l-1)" by auto

        have "(\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. real(k-k'))
            = (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. k-k')" by auto    
        also have "\<dots> = (k-k')*2^(?l-1)" using lulu by simp
     
   finally have absch1stterm:  "(\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. real(k-k'))
                              = real((k-k')*2^(?l-1))" .
 
      text "Transformation of the second term"       
 

        let ?S="{(xs'!j)|j. j<k'}"

        from queryinlist have "q \<in> set (swaps (paid_A ! n) (s_A n))" by auto
        then have "index (swaps (paid_A ! n) (s_A n)) q < length xs'" by auto
        then have k'inbound: "k' < length xs'" by auto 
        
        { fix x
          have a: "{..<k'} = {j. j<k'}" by auto
          have b: "?S = ((%j. xs'!j) ` {j. j<k'})" by auto

          have "(\<Sum>j<k'. (\<lambda>t. (if x!(index init t) then 2::real else 1)) (xs'!j))
            = sum ((\<lambda>t. (if x!(index init t) then 2::real else 1)) o (%j. xs'!j)) {..<k'}"
              by(auto)
          also have "\<dots> = sum ((\<lambda>t. (if x!(index init t) then 2::real else 1)) o (%j. xs'!j)) {j. j<k'}"
              by (simp only: a)
          also have "\<dots> = sum (\<lambda>t. (if x!(index init t) then 2::real else 1)) ((%j. xs'!j) ` {j. j<k'})"
              apply(rule sum.reindex[symmetric])
              apply(rule inj_on_nth)
                using k'inbound by(simp_all)
          finally have "(\<Sum>j<k'. (\<lambda>t. (if x!(index init t) then 2::real else 1)) (xs'!j))                   
                  = (\<Sum>j\<in>?S. (\<lambda>t. (if x!(index init t) then 2 else 1)) j)" using b by simp              
        } note reindex=this

        have identS: "?S = set (take k' xs')"
          proof -
              have "index (swaps (paid_A ! n) (s_A n)) (q) \<le> length (swaps (paid_A ! n) (s_A n))"
                  by (rule index_le_size)
              then have kxs': "k' \<le> length xs'" by simp
              have "?S = (!) xs' ` {0..<k'}" by force
              also have "\<dots> = set (take k' xs')" apply(rule nth_image) by(rule kxs')
              finally show "?S = set (take k' xs')" .
          qed
        have distinctS: "distinct (take k' xs')" using distinct_take identS by simp
        have lengthS: "length (take k' xs') = k'" using length_take k'inbound by simp
        from distinct_card[OF distinctS] lengthS have "card (set (take k' xs')) = k'" by simp
        then have cardS: "card ?S = k'" using identS by simp
        
        have a: "?S \<subseteq> set xs'" using set_take_subset identS by metis
        then have Ssubso: "(index init) ` ?S \<subseteq> {0..<?l}" using setinit by auto
        from a have s_subst_init: "?S \<subseteq> set init" by auto
        
        note index_inj_on_S=subset_inj_on[OF inj_on_index[of "init"] s_subst_init]

        have l: "xs'!k = q" unfolding k_def apply(rule nth_index) using queryinlist by(auto)
        have "xs'!k \<notin> set (take k' xs')"
            apply(rule index_take) using l by simp
        then have requestnotinS: "(q) \<notin> ?S" using l identS by simp
        then have indexnotin: "index init q \<notin> (index init) ` ?S"
            using index_inj_on_S s_subst_init by auto
       

        have lua: "{l. length l = ?l \<and> ~l!(index init q)}
            = {xs. (\<forall>i\<in>{}. xs ! i) \<and> (\<forall>i\<in>{index init q}. \<not> xs ! i) \<and> length xs = ?l}" by auto


        from k'inbound have k'inbound2: "Suc k' \<le> length init" using Suc_le_eq by auto

        (* rewrite from sum over indices of the list 
            to sum over elements (thus indices of the bit vector) *)
        have "(\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. (\<Sum>j<k'. (if x!(index init (xs'!j)) then 2::real else 1)))
                     
                = (\<Sum>x\<in>{l. length l = ?l \<and> ~l!(index init q)}. (\<Sum>j\<in>?S. (\<lambda>t. (if x!(index init t) then 2 else 1)) j))"
                using reindex by auto
        
        (* rewrite to conform the syntax of  Expactation2or1 *)
        also
        have "\<dots> = (\<Sum>x\<in>{xs. (\<forall>i\<in>{}. xs ! i) \<and> (\<forall>i\<in>{index init q}. \<not> xs ! i) \<and> length xs = ?l}. (\<Sum>j\<in>?S. (\<lambda>t. (if x!(index init t) then 2 else 1)) j))" 
          using lua by auto   
        also
        have "\<dots> = (\<Sum>x\<in>{xs. (\<forall>i\<in>{}. xs ! i) \<and> (\<forall>i\<in>{index init q}. \<not> xs ! i) \<and> length xs = ?l}. (\<Sum>j\<in>(index init) ` ?S. (\<lambda>t. (if x!t then 2 else 1)) j))" 
        proof -
          { fix x
          have "(\<Sum>j\<in>?S. (\<lambda>t. (if x!(index init t) then 2 else 1)) j)
              = (\<Sum>j\<in>(index init) ` ?S. (\<lambda>t. (if x!t then 2 else 1)) j)"
                apply(simp only: sum.reindex[OF index_inj_on_S, where g="(%j. if x ! j then 2 else 1)"])
                by(simp) 
          } note a=this
          show ?thesis by(simp only: a)
        qed

        (* use  Expactation2or1, and solve all the conditions *)
        also
        have "\<dots> = 3 / 2 * real (card ?S) * 2 ^ (?l - card {} - card {q})"
          apply(subst Expactation2or1)
            apply(simp)
            apply(simp)
            apply(simp)
            apply(simp only: card_image index_inj_on_S cardS ) apply(simp add: k'inbound2 del: k'_def)
            using indexnotin apply(simp add: )
            apply(simp)
            using Ssubso queryinlist apply(simp)
            apply(simp only: card_image[OF index_inj_on_S]) by simp 
        finally have "(\<Sum>x\<in>{l. length l = ?l \<and> \<not> l ! (index init q)}. \<Sum>j<k'. if x ! (index init (xs' ! j)) then 2 else 1)
        = 3 / 2 *  real (card ?S) * 2 ^ (?l - card {} - card {q}) " .

        (* insert the cardinality of S*)
        also
        have "3 / 2 *  real (card ?S) *  2 ^ (?l - card {} - card {q}) = (3/2) * (real (k')) *  2 ^ (?l - 1)" using cardS by auto

        finally have absch2ndterm: " (\<Sum>x\<in>{l. length l = ?l \<and>  \<not> l ! (index init q)}.
                              \<Sum>j<k'. if x !(index init (xs' ! j)) then 2 else 1) =
                              3 / 2 * real (k') * 2 ^ (?l - 1) " .
 

      text "Equational transformations to the goal" 

      have cardonebitset: "card {l::bool list. length l = ?l \<and> l!(index init q)} = 2^(?l-1)" using lulu by auto

      have splitie: "{l::bool list. length l = ?l}
            = {l::bool list. length l = ?l \<and> l!(index init q)} \<union> {l::bool list. length l = ?l \<and> ~l!(index init q)}"
            by auto
      have interempty: "{l::bool list. length l = ?l \<and> l!(index init q)} \<inter> {l::bool list. length l = ?l \<and> ~l!(index init q)}
            = {}" by auto
      have fa: "finite {l::bool list. length l = ?l \<and> l!(index init q)}" using bitstrings_finite by auto
      have fb: "finite {l::bool list. length l = ?l \<and> ~l!(index init q)}" using bitstrings_finite by auto

      { fix f :: "bool list \<Rightarrow> real"
        have "(\<Sum>x\<in>{l::bool list. length l = ?l}. f x)
        = (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)} \<union> {l::bool list. length l = ?l \<and> ~l!(index init q)}. f x)" by(simp only: splitie)
        also have "\<dots>
            =     (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. f x)
                              + (\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. f x)
                              - (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)} \<inter> {l::bool list. length l = ?l \<and> ~l!(index init q)}. f x)"
        using sum_Un[OF fa fb, of "f"] by simp
        also have "\<dots> = (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. f x)
                              + (\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. f x)" by(simp add: interempty)
        finally have "sum f {l. length l = length init} =
  sum f {l. length l = length init \<and> l ! (index init q)} + sum f {l. length l = length init \<and> \<not> l ! (index init q)}" .
      } note darfstsplitten=this



      have E1: "E(map_pmf (\<lambda>x. (if (fst (snd x))!(index init q) then real(k-k') else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1)))) D)
          = E(map_pmf (\<lambda>x. (if x!(index init q) then real(k-k') else (\<Sum>j<k'. (if x!(index init (xs'!j)) then 2::real else 1)))) (map_pmf (fst \<circ> snd) D))"
          proof -
            have triv: "\<And>x. (fst \<circ> snd) x = fst (snd x)" by simp 
            have "E((map_pmf (\<lambda>x. (if (fst (snd x))!(index init q) then real(k-k') else (\<Sum>j<k'. (if (fst (snd x))!index init (xs'!j) then 2::real else 1))))) D)
                = E(map_pmf (\<lambda>x. ((\<lambda>y. (if y!(index init q) then real(k-k') else (\<Sum>j<k'. (if y!index init (xs'!j) then 2::real else 1)))) \<circ> (fst \<circ> snd)) x) D)"
                apply(auto simp: comp_assoc) by (simp only: triv)
            also have "\<dots> = E((map_pmf (\<lambda>x. (if x!(index init q) then real(k-k') else (\<Sum>j<k'. (if x!index init (xs'!j) then 2::real else 1)))) \<circ> (map_pmf (fst \<circ> snd))) D)" 
                using map_pmf_compose by metis
            also have "\<dots> = E(map_pmf (\<lambda>x. (if x!(index init q) then real(k-k') else (\<Sum>j<k'. (if x!index init (xs'!j) then 2::real else 1)))) (map_pmf (fst \<circ> snd) D))" by auto
            finally show ?thesis .
          qed
      also
      have E2:  "\<dots> = E(map_pmf (\<lambda>x. (if x!(index init q) then real(k-k') else (\<Sum>j<k'. (if x!(index init (xs'!j)) then 2::real else 1)))) (bv ?l))"
          using config_n_bv[of init _] by auto
      also
      let ?insf="(\<lambda>x. (if x!(index init q) then k-k' else (\<Sum>j<k'. (if x!(index init (xs'!j)) then 2::real else 1))))"
      have E3: "\<dots> = (\<Sum>x\<in>(set_pmf (bv ?l)). (?insf x) * pmf (bv ?l) x)"
        by (subst E_finite_sum_fun) (auto simp: bv_finite mult_ac)
      also
      have "\<dots> = (\<Sum>x\<in>{l::bool list. length l = ?l}. (?insf x) * pmf (bv ?l) x)"
      using bv_set by auto
      also
      have E4: "\<dots> = (\<Sum>x\<in>{l::bool list. length l = ?l}. (?insf x) * (1/2)^?l)"
      using list_pmf by auto
      also
      have "\<dots> = (\<Sum>x\<in>{l::bool list. length l = ?l}. (?insf x)) * ((1/2)^?l)"
      by(simp only: sum_distrib_right[where r="(1/2)^?l"])
      also
      have E5: "\<dots> = ((1/2)^?l) *(\<Sum>x\<in>{l::bool list. length l = ?l}. (?insf x))"
      by(auto)
      also
      have E6: "\<dots> = ((1/2)^?l) * (  (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. ?insf x)
                              + (\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. ?insf x)
                             )" using darfstsplitten by auto
      also
      have E7: "\<dots> = ((1/2)^?l) * (  (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. ((\<lambda>x. real(k-k'))) x)
                              + (\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. ((\<lambda>x. (\<Sum>j<k'. (if x!index init (xs'!j) then 2::real else 1)))) x)
                             )" by auto
      finally have "E(map_pmf (\<lambda>x. (if (fst (snd x))!(index init q) then real(k-k') else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1)))) D)
            = ((1/2)^?l) * (  (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. ((\<lambda>x. real(k-k'))) x)
                              + (\<Sum>x\<in>{l::bool list. length l = ?l \<and> ~l!(index init q)}. ((\<lambda>x. (\<Sum>j<k'. (if x!(index init (xs'!j)) then 2::real else 1)))) x)
                             )" .
      also
      have "\<dots> = ((1/2)^?l) * (  (\<Sum>x\<in>{l::bool list. length l = ?l \<and> l!(index init q)}. real(k-k'))
                              + (3/2)*(real (k'))*2^(?l-1)
                             )" by(simp only: absch2ndterm)
      also
      have E8: "\<dots> = ((1/2)^?l) * ( real((k-k')*2^(?l-1)) + (3/2)*(real (k'))*2^(?l-1))"
          by(simp only: absch1stterm)
      (* from here it is only arithmetic ... *)
      also have "\<dots> = ((1/2)^?l) * ( (  (k-k') + (k')*(3/2)  ) * 2^(?l-1) )" apply(simp only: distrib_right) by simp
      also have "\<dots> = ((1/2)^?l) * 2^(?l-1) * (   (k-k') + (k')*(3/2)    )" by simp
      also have "\<dots> = (((1::real)/2)^(Suc l')) * 2^(l') * (   real(k-k') + (k')*(3/2)    )"
      using lSuc by auto (* REFACTOR: the only place where I use lSuc , can I avoid it? 
                yes, if ?l=0 then k=k'<?l impossible, perhaps I can insert that
                  somehow ? 
              *)
      also have E9: "\<dots> = (1/2) *   (   real(k-k') + (k')*(3/2)    )"
      proof - 
        have "((1::real)/2)^l' * 2^l'  = ((1::real)/2 * 2)^l' " by(rule power_mult_distrib[symmetric])
        also have "...   = 1" by auto
        finally have "(((1::real)/2)^(Suc l'))* 2^l'=(1/2)" by auto
        then show ?thesis by auto
      qed      
      also have E10: "\<dots> \<le> (1/2) * (  (3/2)*(k-k') + (k')*(3/2)  )" by auto (* and one inequality *)
      also have "\<dots> = (1/2) * (  (3/2)*(k-k'+(k'))  )" by auto
      also have "\<dots> = (1/2) * (  (3/2)*(k)  )" by auto
      also have E11: "\<dots> = (3/4)*(k )" by auto
      finally show "E(map_pmf (\<lambda>x. (if q \<in> set init then (if (fst (snd x))!(index init q) then real( k-k' ) else (\<Sum>j<k'. (if (fst (snd x))!index init (xs'!j) then 2::real else 1))) else 0 )) D)
          \<le> 3/4 * k " using True by simp    
 
    qed (* free_absch *)
 


text "Transformation of the Term for Paid Exchanges"
 
    have paid_absch: "E(map_pmf (\<lambda>x. (\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2::real else 1) )) D) = 3/2 * (length (paid_A!n))"
    proof - 

      {
        fix i
        assume inbound: "(index init i) < length init"
        have "map_pmf (\<lambda>xx. if fst (snd xx) ! (index init i) then 2::real else 1) D =
                  bind_pmf (map_pmf (fst \<circ> snd) D) (\<lambda>b. return_pmf (if b! index init i then 2::real else 1))"
                            unfolding map_pmf_def by(simp add: bind_assoc_pmf bind_return_pmf)
        also have "\<dots> = bind_pmf (bv (length init)) (\<lambda>b. return_pmf (if b! index init i then 2::real else 1))"
                    using config_n_bv[of init "take n qs"] by simp 
        also have "\<dots> = map_pmf (\<lambda>yy. (if yy then 2 else 1)) ( map_pmf (\<lambda>y. y!(index init i)) (bv (length init)))"
              by (simp add: map_pmf_def bind_return_pmf bind_assoc_pmf)    
        also have "\<dots> = map_pmf (\<lambda>yy. (if yy then 2 else 1)) (bernoulli_pmf (5 / 10))"
               by (auto simp add:  bv_comp_bernoulli[OF inbound]) 
        finally have "map_pmf (\<lambda>xx. if fst (snd xx) ! (index init i) then 2::real else 1) D =
                      map_pmf (\<lambda>yy. if yy then 2::real else 1) (bernoulli_pmf (5 / 10)) " .
      } note umform = this
    
    
      have "E(map_pmf (\<lambda>x. (\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2::real else 1))) D) = 
          (\<Sum>i<(length (paid_A!n)). E(map_pmf ((\<lambda>xx. (if (fst (snd xx))!(gebub n i) then 2::real else 1))) D))"
          apply(subst E_linear_sum2)
            using finite_config_BIT[OF dist_init] by(simp_all)
      also have "\<dots> =  (\<Sum>i<(length (paid_A!n)). E(map_pmf (\<lambda>y. if y then 2::real else 1) (bernoulli_pmf (5 / 10))))" using umform gebub_def gebub_inBound[OF 31] by simp
      also have "\<dots> =  3/2 * (length (paid_A!n))" by(simp add: E_bernoulli)
      finally show "E(map_pmf (\<lambda>x. (\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2::real else 1))) D) = 3/2 * (length (paid_A!n))" .
    qed
    
text "Combine the Results"
 
    (* cost of A *)
    have costA_absch: "k+(length (paid_A!n)) + 1 = t_A n" unfolding k_def q_def c_A_def p_A_def t_A_def by (auto)

    (* combine *)
    let  ?yo= "(\<lambda>x. (cost x) + (\<Phi>\<^sub>2 x) - (\<Phi>\<^sub>0 x))"
    let ?yo2=" (\<lambda>x. (k + 1) + (if (q)\<in>set init then (if (fst (snd x))!(index init q) then k-k' 
                                              else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1)) ) else 0)
                                                  +(\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2 else 1)))"
 
    have E0: "t_BIT n + Phi(n+1) - Phi n = E (map_pmf ?yo D) "
      using inEreinziehn by auto
    also have "\<dots> \<le> E(map_pmf ?yo2 D)"
           apply(rule E_mono2) unfolding D_def
            apply(fact finite_config_BIT[OF dist_init])
            apply(fact ub_cost[unfolded D_def])
            done

    also have E2: "\<dots> = E(map_pmf (\<lambda>x. k + 1::real) D)
            + (E(map_pmf (\<lambda>x. (if (q)\<in>set init then (if (fst (snd x))!(index init q) then real(k-k') else (\<Sum>j<k'. (if (fst (snd x))!(index init (xs'!j)) then 2::real else 1)))else 0)) D)
            + E(map_pmf (\<lambda>x. (\<Sum>i<(length (paid_A!n)). (if (fst (snd x))!(gebub n i) then 2::real else 1))) D))"
             unfolding D_def  apply(simp only: E_linear_plus2[OF finite_config_BIT[OF dist_init]]) by(auto simp: add.assoc)
 
    also have E3: "\<dots> \<le>  k + 1 + (3/4 * (real (k)) + (3/2 * real (length (paid_A!n))))" using paid_absch free_absch by auto

    also have "\<dots> = k + (3/4 * (real k)) + 1  + 3/2 *(length (paid_A!n)) " by auto  (* arithmetic! *)
    also have "\<dots> = (1+3/4) * (real k) + 1  + 3/2 *(length (paid_A!n)) " by auto  (* arithmetic! *)
    also have E4: "\<dots> = 7/4*(real k) + 3/2 *(length (paid_A!n)) + 1 " by auto (* arithmetic! *)
    also have "\<dots> \<le> 7/4*(real k) + 7/4 *(length (paid_A!n)) + 1" by auto (* arithmetic! *)
    also have E5:"\<dots> = 7/4*(k+(length (paid_A!n))) + 1 " by auto
    also have E6:"\<dots> = 7/4*(t_A n - (1::real)) + 1" using costA_absch by auto
    also have "\<dots> = 7/4*(t_A n) - 7/4 + 1" by algebra
    also have E7: "\<dots> = 7/4*(t_A n)- 3/4" by auto
    finally  show "t_BIT n + Phi(n+1) - Phi n \<le> (7 / 4) * t_A n - 3/4" .
  qed
  then show "t_BIT n + Phi(n + 1) - Phi n \<le> (7 / 4) * t_A n - 3/4" .
qed

subsubsection "Lift the Result to the Whole Request List"

 
lemma T_BIT_absch_le: assumes nqs: "n \<le> length qs"
  shows "T_BIT n \<le> (7 / 4) * T_A n - 3/4*n"
unfolding T_BIT_def T_A_def
proof - 
  from potential2[of "Phi", OF phi0 phi_pos myub] nqs have
      "sum t_BIT {..<n} \<le> (\<Sum>i<n. 7 / 4 *   (t_A i) - 3 / 4)" by auto
  also have "\<dots> = (\<Sum>i<n. 7 / 4 * real_of_int (t_A i)) - (\<Sum>i<n. (3/4))" by (rule sum_subtractf)
  also have "\<dots> = (\<Sum>i<n. 7 / 4 * real_of_int (t_A i)) - (3/4)*(\<Sum>i<n. 1)" by simp
  also have "\<dots> = (\<Sum>i<n. (7 / 4) * real_of_int (t_A i)) - (3/4)*n" by simp
  also have "\<dots> =  (7 / 4) * (\<Sum>i<n. real_of_int (t_A i))  - (3/4)*n" by (simp add: sum_distrib_left)
  also have "\<dots> = (7 / 4) * real_of_int (\<Sum>i<n.(t_A i))  - (3/4)*n" by auto
  finally show "sum t_BIT {..<n} \<le> 7 / 4 * real_of_int (sum t_A {..<n})  - (3/4)*n" by auto
qed 



lemma T_BIT_absch: assumes nqs: "n \<le> length qs"
  shows "T_BIT n \<le> (7 / 4) * T_A' n - 3/4*n"
using nqs T_BIT_absch_le[of n] T_A_A'_leq[of n] by auto

lemma T_A_nneg: "0 \<le> T_A n"
by(auto simp add: sum_nonneg T_A_def t_A_def c_A_def p_A_def)

 

lemma T_BIT_eq: "T_BIT (length qs) = T_on_rand BIT init qs"
unfolding T_BIT_def T_on_rand_as_sum using t_BIT_def  by auto


corollary T_BIT_competitive: assumes "n \<le> length qs" and "init \<noteq> []" and "\<forall>i<n. qs!i \<in> set init"
shows "T_BIT n \<le> ((7 / 4) - 3/(4 * size init)) * T_A' n"
proof cases
  assume 0: "real_of_int(T_A' n) \<le> n * (size init)"
  then have 1: "3/4*real_of_int(T_A' n) \<le> 3/4*(n * (size init))" by auto
  have "T_BIT n \<le> (7 / 4) * T_A' n - 3/4*n" using T_BIT_absch[OF assms(1)] by auto
  also have "\<dots> = ((7 / 4) * real_of_int(T_A' n)) - (3/4*(n * size init)) / size init"
    using assms(2) by simp
  also have "\<dots> \<le> ((7 / 4) * real_of_int(T_A' n)) - 3/4*T_A' n / size init"
    by(rule diff_left_mono[OF  divide_right_mono[OF 1]]) simp
  also have "\<dots> = ((7 / 4) - 3/4 / size init) * T_A' n" by algebra
  also have "\<dots> = ((7 / 4) - 3/(4 * size init)) * T_A' n" by simp
  finally show ?thesis .
next
  assume 0: "\<not> real_of_int(T_A' n) \<le> n * (size init)"

  have T_A'_nneg: "0 \<le> T_A' n" using T_A_nneg[of n] T_A_A'_leq[of n] assms(1) by auto

  have "2 - 1 / size init \<ge> 1" using assms(2)
    by (auto simp add: field_simps neq_Nil_conv)
  have " T_BIT n  \<le> n * size init" using T_BIT_ub[OF assms(3)] by linarith
  also have "\<dots> < real_of_int(T_A' n)" using 0 by linarith
  also have "\<dots> \<le> ((7 / 4) - 3/4 / size init) * T_A' n" using assms(2) T_A'_nneg
    by(auto simp add: mult_le_cancel_right1 field_simps neq_Nil_conv)
  finally show ?thesis by simp
qed


lemma t_A'_t: "n < length qs \<Longrightarrow> t_A' n = int (t (s_A' n) (qs!n) (acts ! n))"
by (simp add: t_A'_def t_def c_A'_def p_A'_def paid_A'_def len_acts split: prod.split)

lemma T_A'_eq_lem: "(\<Sum>i=0..<length qs. t_A' i) =
  T (s_A' 0) (drop 0 qs) (drop 0 acts)"
proof(induction rule: zero_induct[of _ "size qs"])
  case 1 thus ?case by (simp add: len_acts)
next
  case (2 n)
  show ?case
  proof cases
    assume "n < length qs"
    thus ?case using 2
    by(simp add: Cons_nth_drop_Suc[symmetric,where i=n] len_acts sum.atLeast_Suc_lessThan
      t_A'_t free_A_def paid_A'_def)
  next
    assume "\<not> n < length qs" thus ?case by (simp add: len_acts)
  qed
qed

lemma T_A'_eq: "T_A' (length qs) = T init qs acts"
using T_A'_eq_lem by(simp add: T_A'_def atLeast0LessThan)

corollary BIT_competitive3: "init \<noteq> [] \<Longrightarrow> \<forall>i<length qs. qs!i \<in> set init \<Longrightarrow>
  T_BIT (length qs) \<le> ( (7/4) - 3 / (4 * length init)) * T init qs acts"
using order.refl T_BIT_competitive[of "length qs"] T_A'_eq by (simp add: of_int_of_nat_eq)

corollary BIT_competitive2: "init \<noteq> [] \<Longrightarrow> \<forall>i<length qs. qs!i \<in> set init \<Longrightarrow>
  T_on_rand BIT init qs \<le> ( (7/4) - 3 / (4 * length init)) * T init qs acts"
using BIT_competitive3 T_BIT_eq by auto

corollary BIT_absch_le: "init \<noteq> [] \<Longrightarrow>
  T_on_rand BIT init qs \<le> (7 / 4) * (T init qs acts) - 3/4 * length qs"
using T_BIT_absch[of "length qs", unfolded T_A'_eq T_BIT_eq] by auto
 
end
 

subsubsection "Generalize Competitivness of BIT"
 

lemma setdi: "set xs = {0..<length xs} \<Longrightarrow> distinct xs"
apply(rule card_distinct) by auto


theorem compet_BIT: assumes "init \<noteq> []" "distinct init" "set qs \<subseteq> set init"  
shows "T_on_rand BIT init qs \<le> ( (7/4) - 3 / (4 * length init)) * T_opt init qs"
proof-
  from assms(3) have 1: "\<forall>i < length qs. qs!i \<in> set init" by auto
  { fix acts :: "answer list" 
    assume len: "length acts = length qs"
    interpret BIT_Off acts qs init proof qed (auto simp: assms(2) len)
    from BIT_competitive2[OF assms(1) 1] assms(1)
    have "T_on_rand BIT init qs / ( (7/4) - 3 / (4 * length init)) \<le> real(T init qs acts)"
      by(simp add: field_simps length_greater_0_conv[symmetric]
        del: length_greater_0_conv) }
    hence "T_on_rand BIT init qs / ( (7/4) - 3 / (4 * length init)) \<le> T_opt init qs"
      apply(simp add: T_opt_def Inf_nat_def)
      apply(rule LeastI2_wellorder)
      using length_replicate[of "length qs" undefined] apply fastforce
      apply auto
      done
  thus ?thesis using assms by(simp add: field_simps
    length_greater_0_conv[symmetric] del: length_greater_0_conv)
qed
 
theorem compet_BIT4: assumes "init \<noteq> []" "distinct init"   
shows "T_on_rand BIT init qs \<le> 7/4 * T_opt init qs"
proof- 
  { fix acts :: "answer list" 
    assume len: "length acts = length qs"
    interpret BIT_Off acts qs init proof qed (auto simp: assms(2) len)
    from BIT_absch_le[OF assms(1)] assms(1)
    have "(T_on_rand BIT init qs + 3 / 4 * length qs)/ (7/4) \<le> real(T init qs acts)"
      by(simp add: field_simps length_greater_0_conv[symmetric]
        del: length_greater_0_conv) }
    hence "(T_on_rand BIT init qs + 3 / 4 * length qs)/ (7/4) \<le> T_opt init qs"
      apply(simp add: T_opt_def Inf_nat_def)
      apply(rule LeastI2_wellorder)
      using length_replicate[of "length qs" undefined] apply fastforce
      apply auto
      done
  thus ?thesis by(simp add: field_simps
    length_greater_0_conv[symmetric] del: length_greater_0_conv)
qed
 
theorem compet_BIT_2:
 "compet_rand BIT (7/4) {init. init \<noteq> [] \<and> distinct init}"
unfolding compet_rand_def
proof 
  fix init
  assume "init \<in> {init. init \<noteq> [] \<and> distinct init }"
  then have ne: "init \<noteq> []" and  a: "distinct init" by auto
  {
    fix qs
    assume "init \<noteq> []" and a: "distinct init"
    then have "T_on_rand BIT init qs \<le> 7/4 * T_opt init qs"
      using compet_BIT4[of init qs] by simp
  }
  with a ne  show "\<exists>b\<ge>0. \<forall>qs. static init qs \<longrightarrow> T_on_rand BIT init qs  \<le>  (7 / 4) * (T_opt init qs) + b"
    by auto
qed
  
end
