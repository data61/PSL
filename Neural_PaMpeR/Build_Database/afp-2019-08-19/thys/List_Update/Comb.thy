(*  Title:       COMB
    Author:      Max Haslbeck
*) 

section "COMB"

theory Comb
imports TS BIT_2comp_on2 BIT_pairwise
begin


(*  state of BIT: bool list     bit string
    state of TS: nat list       history
*)

subsection "Definition of COMB"

type_synonym CombState = "(bool list * nat list) + (nat list)" 
                          
definition COMB_init :: "nat list \<Rightarrow> (nat state, CombState) alg_on_init" where
  "COMB_init h init = 
        Sum_pmf 0.8 (fst BIT init) (fst (embed (rTS h)) init)"

lemma COMB_init[simp]: "COMB_init h init =
                do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8);
                    (xs::bool list) \<leftarrow> Prob_Theory.bv (length init);
                    return_pmf (if b then Inl (xs, init) else Inr h)
                  }" 
 apply(simp add: bind_return_pmf COMB_init_def BIT_init_def rTS_def
              bind_assoc_pmf )
 unfolding map_pmf_def Sum_pmf_def
 apply(simp add: if_distrib bind_return_pmf bind_assoc_pmf )
    apply(rule bind_pmf_cong) 
     by(auto simp add: bind_return_pmf bind_assoc_pmf)

definition COMB_step :: "(nat state, CombState, nat, answer) alg_on_step" where
"COMB_step s q = (case snd s of Inl b \<Rightarrow> map_pmf (\<lambda>((a,b),c). ((a,b),Inl c)) (BIT_step (fst s, b) q)
                              | Inr b \<Rightarrow> map_pmf (\<lambda>((a,b),c). ((a,b),Inr c)) (return_pmf (TS_step_d (fst s, b) q)))"
            
definition "COMB h = (COMB_init h, COMB_step)"
 

subsection "Comb 1.6-competitive on 2 elements"
 
abbreviation "noc == (%x. case x of Inl (s,is) \<Rightarrow> (s,Inl is) | Inr (s,is) \<Rightarrow> (s,Inr is) )"
abbreviation "con == (%(s,is). case is of Inl is \<Rightarrow> Inl (s,is) | Inr is \<Rightarrow> Inr (s,is) )"

definition "inv_COMB s x i == (\<exists>Da Db. finite (set_pmf Da) \<and> finite (set_pmf Db) \<and>
      (map_pmf con s) = Sum_pmf 0.8 Da Db \<and> BIT_inv Da x i \<and> TS_inv Db x i)"

lemma noccon: "noc o con = id"
  apply(rule ext)
  apply(case_tac x) by(auto simp add: sum.case_eq_if)
 
lemma connoc: "con o noc = id"
  apply(rule ext)
  apply(case_tac x) by(auto simp add: sum.case_eq_if) 

lemma obligation1': assumes "map_pmf con s = Sum_pmf (8 / 10) Da Db"
    shows "config'_rand (COMB h) s qs =
    map_pmf noc (Sum_pmf (8 / 10) (config'_rand BIT Da qs)
                     (config'_rand (embed (rTS h)) Db qs))"
proof (induct qs rule: rev_induct) 
  case Nil
  have "s = map_pmf noc (map_pmf con s)"
    by(simp add: pmf.map_comp noccon)
also
  from assms have "\<dots> = map_pmf noc (Sum_pmf (8 / 10) Da Db)"
    by simp
finally
  show ?case by simp
next
  case (snoc q qs) 
  show ?case apply(simp)
    apply(subst config'_rand_append)
    apply(subst snoc) 
    apply(simp)
      unfolding Sum_pmf_def
      apply(simp add: 
          bind_assoc_pmf bind_return_pmf COMB_def COMB_step_def)
      apply(subst config'_rand_append)
      apply(subst config'_rand_append)
      apply(simp only: map_pmf_def[where f=noc])
        apply(simp add: bind_return_pmf bind_assoc_pmf)
        apply(rule bind_pmf_cong)
          apply(simp)
         apply(simp only: set_pmf_bernoulli UNIV_bool)
          apply(auto)
            apply(simp only: map_pmf_def[where f=Inl])
            apply(simp add: bind_return_pmf bind_assoc_pmf)
            apply(rule bind_pmf_cong)
            apply(simp add: bind_return_pmf bind_assoc_pmf )
            apply(simp add:  split_def)
            apply(simp add: bind_return_pmf bind_assoc_pmf map_pmf_def)
          apply(simp only: map_pmf_def[where f=Inr])
          apply(simp add: bind_return_pmf bind_assoc_pmf)
          apply(rule bind_pmf_cong)
          apply(simp add: bind_return_pmf bind_assoc_pmf )
          apply(simp add:  split_def)
          apply(simp add: bind_return_pmf bind_assoc_pmf map_pmf_def rTS_def)
  done                
qed 
  
lemma obligation1'': 
    shows "config_rand (COMB h) init qs =
    map_pmf noc (Sum_pmf (8 / 10) (config_rand BIT init qs)
                     (config_rand (embed (rTS h)) init qs))"
apply(rule obligation1')
  apply(simp add: Sum_pmf_def COMB_def map_pmf_def bind_assoc_pmf bind_return_pmf split_def COMB_init_def del: COMB_init)
  apply(rule bind_pmf_cong) 
    by(auto simp add: split_def map_pmf_def bind_return_pmf bind_assoc_pmf)
                                                
lemma obligation1: assumes "map_pmf con s = Sum_pmf (8 / 10) Da Db"
    shows "map_pmf con (config'_rand (COMB []) s qs) = 
    Sum_pmf (8 / 10) (config'_rand BIT Da qs)
                     (config'_rand (embed (rTS [])) Db qs)"
proof -
  from obligation1'[OF assms] have "map_pmf con (config'_rand (COMB []) s qs)
      = map_pmf con (map_pmf noc (Sum_pmf (8 / 10) (config'_rand BIT Da qs)
                     (config'_rand (embed (rTS [])) Db qs)))"
                by simp
also
  have "\<dots> = Sum_pmf (8 / 10) (config'_rand BIT Da qs)
                     (config'_rand (embed (rTS [])) Db qs)"
   apply(simp only: pmf.map_comp connoc) by simp
finally
  show ?thesis .
qed

lemma BIT_config'_fin: "finite (set_pmf s) \<Longrightarrow> finite (set_pmf (config'_rand BIT s qs))"
apply(induct qs rule: rev_induct)
  apply(simp) 
  by(simp add: config'_rand_append BIT_step_def)

lemma TS_config'_fin: "finite (set_pmf s) \<Longrightarrow> finite (set_pmf (config'_rand (embed (rTS h)) s qs))"
apply(induct qs rule: rev_induct)
  apply(simp) 
  by(simp add: config'_rand_append rTS_def TS_step_d_def)

lemma obligation2: assumes "map_pmf con s = Sum_pmf (8 / 10) Da Db"
    and "finite (set_pmf Da)"
    and "finite (set_pmf Db)"
  shows "T\<^sub>p_on_rand' (COMB []) s qs =
    2 / 10 * T\<^sub>p_on_rand' (embed (rTS [])) Db qs +
    8 / 10 * T\<^sub>p_on_rand' BIT Da qs"
proof (induct qs rule: rev_induct)
  case (snoc q qs) 
  have P: "T\<^sub>p_on_rand' (COMB []) (config'_rand (COMB []) s qs) [q]
      = 2 / 10 * T\<^sub>p_on_rand' (embed (rTS [])) (config'_rand (embed (rTS [])) Db qs) [q] +
          8 / 10 * T\<^sub>p_on_rand' BIT (config'_rand BIT Da qs) [q]"
    apply(subst obligation1'[OF assms(1)])
    unfolding Sum_pmf_def
      apply(simp)
      apply(simp only: map_pmf_def[where f=noc])
      apply(simp add: bind_assoc_pmf )
        apply(subst E_bernoulli3)
          apply(simp) apply(simp)  
          apply(simp add: set_pmf_bernoulli)
          apply(simp add: BIT_step_def COMB_def COMB_step_def split_def)
          apply(safe) 
            using BIT_config'_fin[OF assms(2)] apply(simp)
            using TS_config'_fin[OF assms(3)] apply(simp)
          apply(simp)
      apply(simp only: map_pmf_def[where f=Inl])
      apply(simp only: map_pmf_def[where f=Inr])
        apply(simp add: bind_return_pmf bind_assoc_pmf COMB_def COMB_step_def)
        apply(simp add: split_def)
        apply(simp add: rTS_def map_pmf_def bind_return_pmf bind_assoc_pmf COMB_def COMB_step_def)
              
    done

  show ?case
    apply(simp only: T_on_rand'_append)
    apply(subst snoc)
    apply(subst P) by algebra 

qed simp

lemma Combination:
  assumes "qs \<in> pattern" "a \<noteq> b" "{a, b} = {x, y}" "set qs \<subseteq> {a, b}"
    and "inv_COMB s a [x,y]"
    and TS: "\<And>s h. a \<noteq> b \<Longrightarrow> {a, b} = {x, y} \<Longrightarrow> TS_inv s a [x, y] \<Longrightarrow> set qs \<subseteq> {a, b}
      \<Longrightarrow> qs \<in> pattern \<Longrightarrow>
            TS_inv (config'_rand (embed (rTS h)) s qs) (last qs) [x, y] 
          \<and> T\<^sub>p_on_rand' (embed (rTS h)) s qs = ts"
    and BIT: "\<And>s. a \<noteq> b \<Longrightarrow> {a, b} = {x, y} \<Longrightarrow> BIT_inv s a [x, y] \<Longrightarrow> set qs \<subseteq> {a, b}
      \<Longrightarrow> qs \<in> pattern \<Longrightarrow>
            BIT_inv (config'_rand BIT s qs) (last qs) [x, y] 
          \<and> T\<^sub>p_on_rand' BIT s qs = bit"
    and OPT_cost: "a \<noteq> b \<Longrightarrow> qs \<in> pattern \<Longrightarrow> real (T\<^sub>p [a, b] qs (OPT2 qs [a, b])) = opt"
    and absch: "qs \<in> pattern \<Longrightarrow> 0.2 * ts + 0.8 * bit \<le> 1.6 * opt"
  shows "T\<^sub>p_on_rand' (COMB []) s qs \<le> 16 / 10 * real (T\<^sub>p [a, b] qs (OPT2 qs [a, b])) \<and>
    inv_COMB (Partial_Cost_Model.config'_rand (COMB []) s qs) (last qs) [x, y]"
proof -
  let ?D = "map_pmf con s"
  from assms(5) obtain Da Db where Daf: "finite (set_pmf Da)"
      and Dbf: "finite (set_pmf Db)"
      and D: "?D = Sum_pmf 0.8 Da Db"
             and B: "BIT_inv Da a [x,y]" and T: "TS_inv Db a [x,y]"
    unfolding inv_COMB_def by auto 
     

  let ?Da' = "config'_rand BIT Da qs"
  from BIT[OF assms(2,3) B assms(4,1) ]
    have B': "BIT_inv ?Da' (last qs) [x, y]"
    and B_cost: "T\<^sub>p_on_rand' BIT Da qs = bit" by auto

  let ?Db' = "config'_rand (embed (rTS [])) Db qs"
  (* ähnlich *) 
  from TS[OF assms(2,3) T assms(4,1)] 
    have T': "TS_inv ?Db' (last qs) [x, y]"
    and T_cost: "T\<^sub>p_on_rand' (embed (rTS [])) Db qs = ts" by auto 

  have "T\<^sub>p_on_rand' (COMB []) s qs
        = 0.2 * T\<^sub>p_on_rand' (embed (rTS [])) Db qs
            + 0.8 * T\<^sub>p_on_rand' BIT Da qs" 
         using D apply(rule obligation2) apply(fact Daf) apply(fact Dbf) done
also
  have "\<dots>  \<le> 1.6 * opt"
    by (simp only: B_cost T_cost absch[OF assms(1)])
also
  have "\<dots> = 1.6 * T\<^sub>p [a, b] qs (OPT2 qs [a, b])" by (simp add: OPT_cost[OF assms(2,1)]) 
finally
  have Comb_cost: "T\<^sub>p_on_rand' (COMB []) s qs \<le> 1.6 * T\<^sub>p [a, b] qs (OPT2 qs [a, b])" .

  have Comb_inv: "inv_COMB (config'_rand (COMB []) s qs) (last qs) [x, y]"
      unfolding inv_COMB_def
      apply(rule exI[where x="?Da'"])
      apply(rule exI[where x="?Db'"])
        apply(safe)
          apply(rule BIT_config'_fin[OF Daf])
          apply(rule TS_config'_fin[OF Dbf])
          apply(rule obligation1)
          apply(fact D)
          apply(fact B')
          apply(fact T') done

  from Comb_cost Comb_inv show ?thesis by simp
qed

theorem COMB_OPT2':  "(x::nat) \<noteq> y \<Longrightarrow> set \<sigma> \<subseteq> {x,y}
     \<Longrightarrow> T\<^sub>p_on_rand (COMB []) [x,y] \<sigma>  \<le> 1.6 * real (T\<^sub>p_opt [x,y] \<sigma>) + 1.6"
proof (rule Phase_partitioning_general[where P="inv_COMB"], goal_cases)
  case 4
  let ?initBIT ="(map_pmf (Pair [x, y]) (fst BIT [x, y]))"
  let ?initTS ="(map_pmf (Pair [x, y]) (fst (embed (rTS [])) [x, y]))"
  show  "inv_COMB (map_pmf (Pair [x, y]) (fst (COMB []) [x, y])) x [x, y]" 
    unfolding inv_COMB_def
    apply(rule exI[where x="?initBIT"])
    apply(rule exI[where x="?initTS"])
      apply(simp only: BIT_inv_initial[OF 4(1)] )
      apply(simp add: map_pmf_def bind_return_pmf bind_assoc_pmf COMB_def)
      apply(simp add: Sum_pmf_def)
     apply(safe)
         apply(simp add: BIT_init_def)
        apply(rule bind_pmf_cong)
          apply(simp)
          apply(simp add: bind_return_pmf bind_assoc_pmf rTS_def map_pmf_def BIT_init_def)
       apply(simp add: TS_inv_def rTS_def)    
      done
next
  case (5 a b qs s)
  from 5(3)
  show ?case
    proof (rule LxxE, goal_cases)
      case 4
      then show ?thesis apply(rule Combination)
        apply(fact)+
        using TS_a'' apply(simp)
        apply(fact bit_a'')
        apply(fact OPT2_A')
        apply(simp)
      done
    next
      case 1
      then show ?case
        apply(rule Combination)
        apply(fact)+
        apply(fact TS_d'') 
        apply(fact bit_d')
        by auto
    next
      case 2
      then have "qs \<in> lang (seq [Atom b, Atom a, Star (Times (Atom b) (Atom a)), Atom b, Atom b])
              \<or> qs \<in> lang (seq [Atom a, Atom b, Atom a, Star (Times (Atom b) (Atom a)), Atom b, Atom b])" by auto
      then show ?case
        apply(rule disjE)
          apply(erule Combination)
            apply(fact)+
            apply(fact TS_b1'') 
            apply(fact bit_b''1) 
            apply(fact OPT2_B1)
            apply(simp add: ring_distribs)
         apply(erule Combination)
           apply(fact)+
           apply(fact TS_b2'') 
           apply(fact bit_b''2) 
           apply(fact OPT2_B2)
           apply(simp add: ring_distribs)
        done
    next
      case 3
      then have len: "length qs \<ge> 2" by(auto simp add: conc_def)
      have len2: "qs \<in> lang (seq [Atom a, Atom b, Atom a, Star (Times (Atom b) (Atom a)), Atom a]) 
                  \<Longrightarrow> length qs \<ge> 3" by (auto simp add: conc_def)
      from 3 have "qs \<in> lang (seq [Atom b, Atom a, Star (Times (Atom b) (Atom a)), Atom a])
              \<or> qs \<in> lang (seq [Atom a, Atom b, Atom a, Star (Times (Atom b) (Atom a)), Atom a])" by auto
      then show ?case
        apply(rule disjE)
          apply(erule Combination)
            apply(fact)+
            apply(fact TS_c1'')
            apply(fact bit_c''1)  
            apply(fact OPT2_C1)
            using len apply(simp add: ring_distribs)
         apply(erule Combination)
           apply(fact)+
           apply(fact TS_c2'')
           apply(fact bit_c''2)
           apply(fact OPT2_C2)
           using len2 apply(simp add: ring_distribs conc_def)
        done
    qed
qed (simp_all) 


subsection "COMB pairwise"

lemma config_rand_COMB: "config_rand (COMB h) init qs = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8); 
                    (b1,b2) \<leftarrow>  (config_rand BIT init qs);
                    (t1,t2) \<leftarrow>  (config_rand (embed (rTS h)) init qs);
                    return_pmf (if b then  (b1, Inl b2) else (t1, Inr t2))
                    }" (is "?LHS = ?RHS")
proof (induct qs rule: rev_induct)
  case Nil
  show ?case
  apply(simp add: BIT_init_def COMB_def rTS_def map_pmf_def bind_return_pmf bind_assoc_pmf )
  apply(rule bind_pmf_cong)
    apply(simp) 
    apply(simp only: set_pmf_bernoulli)
      apply(case_tac x)
        by(simp_all) 
next
  case (snoc q qs) 
  show ?case apply(simp add: take_Suc_conv_app_nth)
    apply(subst config'_rand_append)
    apply(subst snoc)
      apply(simp)
      apply(simp add: bind_return_pmf bind_assoc_pmf split_def config'_rand_append)
        apply(rule bind_pmf_cong)
          apply(simp) 
          apply(simp only: set_pmf_bernoulli)
            apply(case_tac x)
               by(simp_all add: COMB_def COMB_step_def rTS_def map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
qed

lemma COMB_no_paid: " \<forall>((free, paid), t)\<in>set_pmf (snd (COMB []) (s, is) q). paid = []"
apply(simp add:  COMB_def COMB_step_def split_def BIT_step_def TS_step_d_def)
apply(case_tac "is")
  by(simp_all add: BIT_step_def TS_step_d_def)
  

lemma COMB_pairwise: "pairwise (COMB [])"
proof(rule pairwise_property_lemma, goal_cases) 
  case (1 init qs x y)
  then have qsininit: "set qs \<subseteq> set init" by simp
  
  show "Pbefore_in x y (COMB []) qs init 
        = Pbefore_in x y (COMB []) (Lxy qs {x, y}) (Lxy init {x, y})"
        unfolding Pbefore_in_def
        apply(subst config_rand_COMB)  
        apply(subst config_rand_COMB)  
        apply(simp only: map_pmf_def  bind_assoc_pmf)
        apply(rule bind_pmf_cong)
          apply(simp)
          apply(simp only: set_pmf_bernoulli)
          apply(case_tac xa)
            apply(simp add: split_def) 
              using BIT_pairwise'[OF qsininit 1(3,4,1), unfolded Pbefore_in_def map_pmf_def]
              apply(simp add: bind_return_pmf bind_assoc_pmf)
            apply(simp add: split_def) 
              using TS_pairwise'[OF 1(2,3,4,1), unfolded Pbefore_in_def map_pmf_def]
              by(simp add: bind_return_pmf bind_assoc_pmf)
next
  case (2 xa r)
  show ?case
    using COMB_no_paid
    by (metis (mono_tags) case_prod_unfold surj_pair)  
qed 
          

subsection "COMB 1.6-competitive"

lemma finite_config_TS: "finite (set_pmf (config'' (embed (rTS h)) qs init n))" (is "finite ?D")
  apply(subst config_embed)
    by(simp) 

lemma COMB_has_finite_config_set: assumes [simp]: "distinct init"
      and "set qs \<subseteq> set init" 
      shows "finite (set_pmf (config_rand (COMB h) init qs))"
proof - 
  from finite_config_TS[where n="length qs" and qs=qs]
      finite_config_BIT[OF assms(1)] 
  show ?thesis 
    apply(subst obligation1'')
      by(simp add: Sum_pmf_def)  
qed

theorem COMB_competitive: "\<forall>s0\<in>{x::nat list. distinct x \<and> x\<noteq>[]}.
   \<exists>b\<ge>0. \<forall>qs\<in>{x. set x \<subseteq> set s0}.
             T\<^sub>p_on_rand (COMB []) s0 qs \<le> ((8::nat)/(5::nat)) *  T\<^sub>p_opt s0 qs + b" 
proof(rule factoringlemma_withconstant, goal_cases)
  case 5
  show ?case 
    proof (safe, goal_cases)
      case (1 init)
      note out=this
      show ?case
        apply(rule exI[where x=2])
          apply(simp)
          proof (safe, goal_cases)
            case (1 qs a b)
            then have a: "a\<noteq>b" by simp
            have twist: "{a,b}={b, a}" by auto
            have b1: "set (Lxy qs {a, b}) \<subseteq> {a, b}" unfolding Lxy_def by auto
            with this[unfolded twist] have b2: "set (Lxy qs {b, a}) \<subseteq> {b, a}" by(auto)
        
            have "set (Lxy init {a, b}) = {a,b} \<inter> (set init)" apply(induct init)
                unfolding Lxy_def by(auto)
            with 1 have A: "set (Lxy init {a, b}) = {a,b}" by auto
            have "finite {a,b}" by auto
            from out have B: "distinct (Lxy init {a, b})" unfolding Lxy_def by auto
            have C: "length (Lxy init {a, b}) = 2"
              using distinct_card[OF B, unfolded A] using a by auto
        
            have "{xs. set xs = {a,b} \<and> distinct xs \<and> length xs =(2::nat)} 
                    = { [a,b], [b,a] }"
                  apply(auto simp: a a[symmetric])
                  proof (goal_cases)
                    case (1 xs)
                    from 1(4) obtain x xs' where r:"xs=x#xs'" by (metis Suc_length_conv add_2_eq_Suc' append_Nil length_append)
                    with 1(4) have "length xs' = 1" by auto
                    then obtain y where s: "[y] = xs'" by (metis One_nat_def length_0_conv length_Suc_conv)
                    from r s have t: "[x,y] = xs" by auto
                    moreover from t 1(1) have "x=b" using doubleton_eq_iff 1(2) by fastforce
                    moreover from t 1(1) have "y=a" using doubleton_eq_iff 1(2) by fastforce
                    ultimately show ?case by auto
                  qed
        
            with A B C have pos: "(Lxy init {a, b}) = [a,b]
                  \<or> (Lxy init {a, b}) = [b,a]" by auto
            
            show ?case
              apply(cases "(Lxy init {a, b}) = [a,b]")  
                apply(simp) using COMB_OPT2'[OF a b1] a apply(simp)
                using pos apply(simp) unfolding twist 
              using COMB_OPT2'[OF a[symmetric] b2] by simp
          qed
    qed
next
  case 4  then show ?case using COMB_pairwise by simp
next
  case 7 then show ?case apply(subst COMB_has_finite_config_set[OF 7(1)])
        using set_take_subset apply fast by simp
qed (simp_all add: COMB_no_paid)



theorem COMB_competitive_nice: "compet_rand (COMB []) ((8::nat)/(5::nat)) {x::nat list. distinct x \<and> x\<noteq>[]}"
  unfolding compet_rand_def static_def using COMB_competitive by simp



end
