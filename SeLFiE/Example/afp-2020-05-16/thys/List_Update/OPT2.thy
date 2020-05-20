(*  Title:       Analysis of OPT2
    Author:      Max Haslbeck
*)

section "OPT2"

theory OPT2
imports 
Partial_Cost_Model
RExp_Var
begin

lemma "(N::nat set) \<noteq> {} \<Longrightarrow> Inf N : N"
unfolding Inf_nat_def using LeastI[of "%x. x : N"] by force

lemma nn_contains_Inf:
  fixes S :: "nat set"
  assumes nn: "S \<noteq> {}"
  shows "Inf S \<in> S"
using assms Inf_nat_def LeastI by force


subsection "Definition"

fun OPT2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> (nat * nat list) list" where
  "OPT2 [] [x,y] = []"
| "OPT2 [a] [x,y] = [(0,[])]"
| "OPT2 (a#b#\<sigma>') [x,y] =  (if a=x then (0,[]) # (OPT2 (b#\<sigma>') [x,y])
                                  else (if b=x then (0,[])# (OPT2 (b#\<sigma>') [x,y])
                                               else (1,[])# (OPT2 (b#\<sigma>') [y,x])))"
         

lemma OPT2_length: "length (OPT2 \<sigma> [x, y]) = length \<sigma>"
apply(induct \<sigma> arbitrary: x y)
  apply(simp)
  apply(case_tac \<sigma>) by(auto)

lemma OPT2x: "OPT2 (x#\<sigma>') [x,y] = (0,[])#(OPT2 \<sigma>' [x,y])"
apply(cases \<sigma>') by (simp_all)

 
lemma swapOpt: "T\<^sub>p_opt [x,y] \<sigma> \<le> 1 + T\<^sub>p_opt [y,x] \<sigma>"
proof -
  show ?thesis
  proof (cases "length \<sigma> > 0")
    case True

    have "T\<^sub>p_opt [y,x] \<sigma> \<in> {T\<^sub>p [y, x] \<sigma> as |as. length as = length \<sigma>}"
    unfolding T_opt_def 
      apply(rule nn_contains_Inf)
      apply(auto) by (rule Ex_list_of_length)

    then obtain asyx where costyx: "T\<^sub>p [y,x] \<sigma> asyx = T\<^sub>p_opt [y,x] \<sigma>"
                       and lenyx: "length asyx = length \<sigma>"
              unfolding T_opt_def by auto

    from True lenyx have "length asyx > 0" by auto
    then obtain A asyx' where aa: "asyx = A # asyx'" using list.exhaust by blast
    then obtain m1 a1 where AA: "A = (m1,a1)" by fastforce
    
    let ?asxy = "(m1,a1@[0]) # asyx'"
    
    from True obtain q \<sigma>' where qq: "\<sigma> = q # \<sigma>'" using list.exhaust by blast
  
    have t: "t\<^sub>p [x, y] q (m1, a1@[0]) = Suc (t\<^sub>p [y, x] q (m1, a1))"
    unfolding t\<^sub>p_def
    apply(simp) unfolding swap_def by (simp)
  
    have s: "step [x, y] q (m1, a1 @ [0]) = step [y, x] q (m1, a1)" 
    unfolding step_def mtf2_def by(simp add: swap_def)
  
    have T: "T\<^sub>p [x,y] \<sigma> ?asxy = 1 + T\<^sub>p [y,x] \<sigma> asyx" unfolding qq aa AA by(auto simp add: s t)
   
    have l: "1 + T\<^sub>p_opt [y,x] \<sigma> = T\<^sub>p [x, y] \<sigma> ?asxy" using T costyx by simp
    have "length ?asxy = length \<sigma>" using lenyx aa by auto
    then have inside: "?asxy \<in> {as. size as = size \<sigma>}" by force
    then have b: "T\<^sub>p [x, y] \<sigma> ?asxy \<in> {T\<^sub>p [x, y] \<sigma> as | as. size as = size \<sigma>}" by auto

    then show ?thesis unfolding l unfolding T_opt_def
      apply(rule cInf_lower) by simp
  qed (simp add: T_opt_def)         
qed


lemma tt: "a \<in> {x,y} \<Longrightarrow> OPT2 (rest1) (step [x,y] a (hd (OPT2 (a # rest1) [x, y])))
       = tl (OPT2 (a # rest1) [x, y])"
apply(cases rest1) by(auto simp add: step_def mtf2_def swap_def)

lemma splitqsallg: "Strat \<noteq> [] \<Longrightarrow> a \<in> {x,y} \<Longrightarrow>
         t\<^sub>p [x, y] a (hd (Strat)) +
          (let L=step [x,y] a (hd (Strat)) 
              in T\<^sub>p L (rest1) (tl Strat)) =  T\<^sub>p [x, y] (a # rest1) Strat"
proof -
  assume ne: "Strat \<noteq> []"
  assume axy: "a \<in> {x,y}" (* not needed *)
  have "T\<^sub>p [x, y] (a # rest1) (Strat) 
        = T\<^sub>p [x, y] (a # rest1) ((hd (Strat)) # (tl (Strat)))"
        by(simp only: List.list.collapse[OF ne])
  then show ?thesis by auto
qed

lemma splitqs: "a \<in> {x,y} \<Longrightarrow> T\<^sub>p [x, y] (a # rest1) (OPT2 (a # rest1) [x, y])
        =  t\<^sub>p [x, y] a (hd (OPT2 (a # rest1) [x, y])) +
          (let L=step [x,y] a (hd (OPT2 (a # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))"
proof -
  assume axy: "a \<in> {x,y}"
  have ne: "OPT2 (a # rest1) [x, y] \<noteq> []" apply(cases rest1) by(simp_all)
  have "T\<^sub>p [x, y] (a # rest1) (OPT2 (a # rest1) [x, y]) 
        = T\<^sub>p [x, y] (a # rest1) ((hd (OPT2 (a # rest1) [x, y])) # (tl (OPT2 (a # rest1) [x, y])))"
        by(simp only: List.list.collapse[OF ne])
  also have "\<dots> = T\<^sub>p [x, y] (a # rest1) ((hd (OPT2 (a # rest1) [x, y])) # (OPT2 (rest1) (step [x,y] a (hd (OPT2 (a # rest1) [x, y])))))"
      by(simp only: tt[OF axy])
  also have "\<dots> =   t\<^sub>p [x, y] a (hd (OPT2 (a # rest1) [x, y])) +
          (let L=step [x,y] a (hd (OPT2 (a # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))" by(simp)
  finally show ?thesis .
qed

lemma tpx: "t\<^sub>p [x, y] x (hd (OPT2 (x # rest1) [x, y])) = 0"
by (simp add: OPT2x t\<^sub>p_def)

lemma yup: "T\<^sub>p [x, y] (x # rest1) (OPT2 (x # rest1) [x, y])
        = (let L=step [x,y] x (hd (OPT2 (x # rest1) [x, y])) 
              in T\<^sub>p L (rest1) (OPT2 (rest1) L))"
by (simp add: splitqs tpx)

lemma swapsxy: "A \<in> { [x,y], [y,x]} \<Longrightarrow> swaps sws A \<in> { [x,y], [y,x]}"
apply(induct sws)
  apply(simp)
  apply(simp) unfolding swap_def by auto

lemma mtf2xy: "A \<in> { [x,y], [y,x]} \<Longrightarrow> r\<in>{x,y} \<Longrightarrow> mtf2 a r A \<in> { [x,y], [y,x]}"
by (metis mtf2_def swapsxy)


lemma stepxy: assumes "q \<in> {x,y}" "A \<in> { [x,y], [y,x]}" 
    shows "step A q a \<in> { [x,y], [y,x]}"
unfolding step_def apply(simp only: split_def Let_def)
apply(rule mtf2xy)
  apply(rule swapsxy) by fact+ 


subsection "Proof of Optimality"

lemma OPT2_is_lb: "set \<sigma> \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) \<le> T\<^sub>p_opt [x,y] \<sigma>" 
proof (induct "length \<sigma>" arbitrary: x y \<sigma> rule: less_induct)
  case (less)
  show ?case
  proof (cases \<sigma>)
    case (Cons a \<sigma>')
    note Cons1=Cons
    show ?thesis unfolding Cons
      proof(cases "a=x") (* case that the element in front is requested *)
        case True
        from True Cons have qsform: "\<sigma> = x#\<sigma>'" by auto
        have up: "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (x # \<sigma>')"
          unfolding True
          unfolding T_opt_def apply(rule cInf_greatest)
            apply(simp add: Ex_list_of_length)
            proof -
              fix el
              assume "el \<in> {T\<^sub>p [x, y] (x # \<sigma>') as |as. length as = length (x # \<sigma>')}"
              then obtain Strat where lStrat: "length Strat = length (x # \<sigma>')"
                        and el: "T\<^sub>p [x, y] (x # \<sigma>') Strat = el" by auto
              then have ne: "Strat \<noteq> []" by auto
              let ?LA="step [x,y] x (hd (OPT2 (x # \<sigma>') [x, y]))"
              
              have  E0:  "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y])
                            =T\<^sub>p ?LA (\<sigma>') (OPT2 (\<sigma>') ?LA)" using yup by auto
              also have E1: "\<dots> = T\<^sub>p [x,y] (\<sigma>') (OPT2 (\<sigma>') [x,y])" by (simp add: OPT2x step_def)
              also have E2: "\<dots> \<le>  T\<^sub>p_opt [x,y] \<sigma>'" apply(rule less(1)) using Cons less(2,3) by auto
              also have "\<dots> \<le> T\<^sub>p [x, y] (x # \<sigma>') Strat"
                   proof (cases "(step [x, y] x (hd Strat)) = [x,y]")
                      case True
                      have aha: "T\<^sub>p_opt [x, y] \<sigma>' \<le> T\<^sub>p [x, y] \<sigma>' (tl Strat)"                     
                        unfolding T_opt_def apply(rule cInf_lower)
                          apply(auto) apply(rule exI[where x="tl Strat"]) using lStrat by auto

                      also have E4: "\<dots> \<le> t\<^sub>p [x, y] x (hd Strat) + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" 
                        unfolding True by(simp)
                      also have E5: "\<dots> = T\<^sub>p [x, y] (x # \<sigma>') Strat" using splitqsallg[of Strat x x y \<sigma>', OF ne, simplified]
                        by (auto)
                      finally show ?thesis by auto 
                   next
                      case False
                      have tp1: "t\<^sub>p [x, y] x (hd Strat) \<ge> 1"
                      proof (rule ccontr)
                        let ?a = "hd Strat"
                        assume "\<not> 1 \<le> t\<^sub>p [x, y] x ?a"
                        then have tp0: "t\<^sub>p [x, y] x ?a = 0" by auto
                        then have "size (snd ?a) = 0" unfolding t\<^sub>p_def by(simp add: split_def)
                        then have nopaid: "(snd ?a) = []" by auto
                        have "step [x, y] x ?a = [x, y]"
                          unfolding step_def apply(simp add: split_def nopaid)
                          unfolding mtf2_def by(simp)
                        then show "False" using False by auto
                      qed

                      from False have yx: "step [x, y] x (hd Strat) = [y, x]"
                        using stepxy[where x=x and y=y and a="hd Strat"] by auto

                      have E3: "T\<^sub>p_opt [x, y] \<sigma>' \<le> 1 + T\<^sub>p_opt [y, x] \<sigma>'" using swapOpt by auto
                      also have E4: "\<dots> \<le> 1 + T\<^sub>p [y, x] \<sigma>' (tl Strat)"        
                        apply(simp) unfolding T_opt_def apply(rule cInf_lower)
                          apply(auto) apply(rule exI[where x="tl Strat"]) using lStrat by auto
                      also have E5: "\<dots> = 1 + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" using yx by auto
                      also have E6: "\<dots> \<le> t\<^sub>p [x, y] x (hd Strat) + T\<^sub>p (step [x, y] x (hd Strat)) \<sigma>' (tl Strat)" using tp1 by auto
                      
                      also have E7: "\<dots> = T\<^sub>p [x, y] (x # \<sigma>') Strat" using splitqsallg[of Strat x x y \<sigma>', OF ne, simplified]
                         by (auto)
                      finally show ?thesis by auto
                   qed
              also have "\<dots> = el" using True el by simp
              finally show "T\<^sub>p [x, y] (x # \<sigma>') (OPT2 (x # \<sigma>') [x, y]) \<le> el" by auto        
            qed
         then show "T\<^sub>p [x, y] (a # \<sigma>') (OPT2 (a # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (a # \<sigma>')"
         using True by simp
      next


        case False (* case 2: element at back is requested first *)
        with less Cons have ay: "a=y" by auto
        show "T\<^sub>p [x, y] (a # \<sigma>') (OPT2 (a # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (a # \<sigma>')" unfolding ay
        proof(cases \<sigma>')
          case Nil
          have up: "T\<^sub>p_opt [x, y] [y] \<ge> 1"
            unfolding T_opt_def apply(rule cInf_greatest)
            apply(simp add: Ex_list_of_length)
            proof -
              fix el
              assume "el \<in> {T\<^sub>p [x, y] [y] as |as. length as = length [y]}"
              then obtain Strat where Strat: "length Strat = length [y]" and
                            el: "el = T\<^sub>p [x, y] [y] Strat " by auto
              from Strat obtain a where a: "Strat = [a]" by (metis Suc_length_conv length_0_conv)
              show "1 \<le> el" unfolding el a apply(simp) unfolding t\<^sub>p_def apply(simp add: split_def)
                apply(cases "snd a")
                  apply(simp add: less(3))
                  by(simp)
            qed

          show "T\<^sub>p [x, y] (y # \<sigma>') (OPT2 (y # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (y # \<sigma>')" unfolding Nil
            apply(simp add: t\<^sub>p_def) using less(3) apply(simp)
            using up by(simp)
        next
          case (Cons b rest2)

          show up: "T\<^sub>p [x, y] (y # \<sigma>') (OPT2 (y # \<sigma>') [x, y]) \<le> T\<^sub>p_opt [x, y] (y # \<sigma>')"
            unfolding Cons
          proof (cases "b=x")
            case True
            
            show "T\<^sub>p [x, y] (y # b # rest2) (OPT2 (y # b # rest2) [x, y]) \<le> T\<^sub>p_opt [x, y] (y # b # rest2)"
              unfolding True
              unfolding T_opt_def apply(rule cInf_greatest)
                apply(simp add: Ex_list_of_length)
                proof -
                  fix el
                  assume "el \<in> {T\<^sub>p [x, y] (y # x # rest2) as |as. length as = length (y # x # rest2)}"
                  then obtain Strat where lenStrat: "length Strat = length (y # x # rest2)" and
                               Strat: "el = T\<^sub>p [x, y] (y # x # rest2) Strat" by auto
                  have v: " set rest2 \<subseteq> {x, y}" using less(2)[unfolded Cons1 Cons] by auto
                  
                  let ?L1 = "(step [x, y] y (hd Strat))"
                  let ?L2 = "(step ?L1 x (hd (tl Strat)))"

                  (* lets work on how Strat can look like: *)
                  let ?a1 = "hd Strat"
                  let ?a2 = "hd (tl Strat)"
                  let ?r = "tl (tl Strat)"

                  have "Strat = ?a1 # ?a2 # ?r" by (metis Nitpick.size_list_simp(2) Suc_length_conv lenStrat list.collapse list.discI list.inject)
                  
                  


                  have 1: "T\<^sub>p [x, y] (y # x # rest2) Strat
                        = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p ?L2 rest2 (tl (tl Strat))"  
                    proof - 
                      have a: "Strat \<noteq> []" using lenStrat by auto
                      have b: "(tl Strat) \<noteq> []" using lenStrat by (metis Nitpick.size_list_simp(2) Suc_length_conv list.discI list.inject)

                      have 1: "T\<^sub>p [x, y] (y # x # rest2) Strat
                                = t\<^sub>p [x, y] y (hd Strat) + T\<^sub>p ?L1 (x # rest2) (tl Strat)"
                                  using splitqsallg[OF a, where a=y and x=x and y=y, simplified] by (simp)
                      have tt: "step [x, y] y (hd Strat) \<noteq> [x, y] \<Longrightarrow> step [x, y] y (hd Strat) = [y,x]" 
                        using stepxy[where A="[x,y]"] by blast

                      have 2: "T\<^sub>p ?L1 (x # rest2) (tl Strat) = t\<^sub>p ?L1 x (hd (tl Strat)) +  T\<^sub>p ?L2 (rest2) (tl (tl Strat))"
                                  apply(cases "?L1=[x,y]")
                                    using splitqsallg[OF b, where a=x and x=x and y=y, simplified] apply(auto)
                                    using tt splitqsallg[OF b, where a=x and x=y and y=x, simplified] by auto
                      from 1 2 show ?thesis by auto
                    qed

                  have " T\<^sub>p [x, y] (y # x # rest2) (OPT2 (y # x # rest2) [x, y])
                    =  1 +  T\<^sub>p [x, y] (rest2) (OPT2 (rest2) [x, y])"
                    unfolding True
                    using less(3) by(simp add: t\<^sub>p_def step_def OPT2x)
                  also have "\<dots> \<le> 1 +  T\<^sub>p_opt [x, y] (rest2)" apply(simp)
                    apply(rule less(1))
                      apply(simp add: less(2) Cons1 Cons)
                      apply(fact) by fact
                  also

                  have "\<dots> \<le> T\<^sub>p [x, y] (y # x # rest2) Strat"
                  proof (cases "?L2 = [x,y]")
                    case True
                    have 2: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p [x,y] rest2 (tl (tl Strat)) \<ge> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p_opt [x,y] rest2" apply(simp)
                            unfolding T_opt_def apply(rule cInf_lower)
                            apply(simp) apply(rule exI[where x="tl (tl Strat)"]) by (auto simp: lenStrat)
                    have 3: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))
                            + T\<^sub>p_opt [x,y] rest2 \<ge> 1 + T\<^sub>p_opt [x,y] rest2" apply(simp)
                            proof -
                              have "t\<^sub>p [x, y] y (hd Strat) \<ge> 1"
                              unfolding t\<^sub>p_def apply(simp add: split_def)
                              apply(cases "snd (hd Strat)") by (simp_all add: less(3))
                              then show "Suc 0 \<le> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat))" by auto
                            qed
                    from 1 2 3 True show ?thesis by auto
                  next
                    case False
                    note L2F=this
                    have L1: "?L1 \<in> {[x, y], [y, x]}" apply(rule stepxy) by simp_all
                    have "?L2 \<in> {[x, y], [y, x]}" apply(rule stepxy) using L1 by simp_all
                    with False have 2: "?L2 = [y,x]" by auto

                    have k: "T\<^sub>p [x, y] (y # x # rest2) Strat
                        =   t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat)) +
                            T\<^sub>p [y,x] rest2 (tl (tl Strat))" using 1 2 by auto

                    have l: "t\<^sub>p [x, y] y (hd Strat) > 0"
                        using less(3) unfolding t\<^sub>p_def apply(cases "snd (hd Strat) = []")
                          by (simp_all add: split_def)

                    have r: "T\<^sub>p [x, y] (y # x # rest2) Strat \<ge> 2 + T\<^sub>p [y,x] rest2 (tl (tl Strat))"
                    proof (cases "?L1 = [x,y]")
                      case True
                      note T=this
                      then have "t\<^sub>p ?L1 x (hd (tl Strat)) > 0" unfolding True
                        proof(cases "snd (hd (tl Strat)) = []")
                          case True
                          have "?L2 = [x,y]" unfolding T  apply(simp add: split_def step_def) 
                          unfolding True mtf2_def by(simp)
                          with L2F have "False" by auto
                          then show "0 < t\<^sub>p [x, y] x (hd (tl Strat))" ..
                        next
                          case False
                          then show "0 < t\<^sub>p [x, y] x (hd (tl Strat))"
                            unfolding t\<^sub>p_def by(simp add: split_def)
                        qed                          
                      with l have " t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 x (hd (tl Strat)) \<ge> 2" by auto
                      with k show ?thesis by auto
                    next
                      case False
                      from L1 False have 2: "?L1 = [y,x]" by auto
                      { fix k sws T
                        have "T\<in>{[x,y],[y,x]} \<Longrightarrow> mtf2 k x T = [y,x] \<Longrightarrow> T = [y,x]"
                          apply(rule ccontr) by (simp add: less(3) mtf2_def)
                      }
                      have t1: "t\<^sub>p [x, y] y (hd Strat) \<ge> 1" unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "(snd (hd Strat))") using \<open>x \<noteq> y\<close> by auto
                      have t2: "t\<^sub>p [y,x] x (hd (tl Strat)) \<ge> 1" unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "(snd (hd (tl Strat)))") using \<open>x \<noteq> y\<close> by auto
                      have "T\<^sub>p [x, y] (y # x # rest2) Strat
                          = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p (step [x, y] y (hd Strat)) x (hd (tl Strat)) + T\<^sub>p [y, x] rest2 (tl (tl Strat))"
                            by(rule k)
                      with t1 t2 2 show ?thesis by auto
                    qed
                    have t: "T\<^sub>p [y, x] rest2 (tl (tl Strat)) \<ge> T\<^sub>p_opt [y, x] rest2" 
                      unfolding T_opt_def apply(rule cInf_lower)
                      apply(auto) apply(rule exI[where x="(tl (tl Strat))"]) by(simp add: lenStrat)
                    show ?thesis
                    proof -
                      have "1 + T\<^sub>p_opt [x, y] rest2 \<le> 2 + T\<^sub>p_opt [y, x] rest2"
                      using  swapOpt by auto
                      also have "\<dots> \<le> 2 + T\<^sub>p [y, x] rest2 (tl (tl Strat))" using t by auto
                      also have "\<dots> \<le> T\<^sub>p [x, y] (y # x # rest2) Strat" using r by auto
                      finally show ?thesis .
                    qed
                      
                  qed
                  also have "\<dots> = el" using Strat by auto
                  finally show "T\<^sub>p [x, y] (y # x # rest2) (OPT2 (y # x # rest2) [x, y]) \<le> el" .
                qed


          next
            case False
            with Cons1 Cons less(2) have bisy: "b=y" by auto
            with less(3) have "OPT2 (y # b # rest2) [x, y] = (1,[])# (OPT2 (b#rest2) [y,x])" by simp
            show "T\<^sub>p [x, y] (y # b # rest2) (OPT2 (y # b # rest2) [x, y]) \<le> T\<^sub>p_opt [x, y] (y # b # rest2)" 
              unfolding bisy
              unfolding T_opt_def apply(rule cInf_greatest)
                apply(simp add: Ex_list_of_length)
                proof -
                  fix el
                  assume "el \<in> {T\<^sub>p [x, y] (y # y # rest2) as |as. length as = length (y # y # rest2)}"
                  then obtain Strat where lenStrat: "length Strat = length (y # y # rest2)" and
                               Strat: "el = T\<^sub>p [x, y] (y # y # rest2) Strat" by auto
                  have v: " set rest2 \<subseteq> {x, y}" using less(2)[unfolded Cons1 Cons] by auto

                  let ?L1 = "(step [x, y] y (hd Strat))"
                  let ?L2 = "(step ?L1 y (hd (tl Strat)))"

                  (* lets work on how Strat can look like: *)
                  let ?a1 = "hd Strat"
                  let ?a2 = "hd (tl Strat)"
                  let ?r = "tl (tl Strat)"

                  have "Strat = ?a1 # ?a2 # ?r" by (metis Nitpick.size_list_simp(2) Suc_length_conv lenStrat list.collapse list.discI list.inject)
                  
                  


                  have 1: "T\<^sub>p [x, y] (y # y # rest2) Strat
                        = t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p ?L2 rest2 (tl (tl Strat))" 
                    proof - 
                      have a: "Strat \<noteq> []" using lenStrat by auto
                      have b: "(tl Strat) \<noteq> []" using lenStrat by (metis Nitpick.size_list_simp(2) Suc_length_conv list.discI list.inject)

                      have 1: "T\<^sub>p [x, y] (y # y # rest2) Strat
                                = t\<^sub>p [x, y] y (hd Strat) + T\<^sub>p ?L1 (y # rest2) (tl Strat)"
                                  using splitqsallg[OF a, where a=y and x=x and y=y, simplified] by (simp)
                      have tt: "step [x, y] y (hd Strat) \<noteq> [x, y] \<Longrightarrow> step [x, y] y (hd Strat) = [y,x]" 
                        using stepxy[where A="[x,y]"] by blast
                     
                      have 2: "T\<^sub>p ?L1 (y # rest2) (tl Strat) = t\<^sub>p ?L1 y (hd (tl Strat)) +  T\<^sub>p ?L2 (rest2) (tl (tl Strat))"
                                  apply(cases "?L1=[x,y]")
                                    using splitqsallg[OF b, where a=y and x=x and y=y, simplified] apply(auto)
                                    using tt splitqsallg[OF b, where a=y and x=y and y=x, simplified] by auto
                      from 1 2 show ?thesis by auto
                    qed

                  have " T\<^sub>p [x, y] (y # y # rest2) (OPT2 (y # y # rest2) [x, y])
                    =  1 +  T\<^sub>p [y, x] (rest2) (OPT2 (rest2) [y, x])" 
                    using less(3) by(simp add: t\<^sub>p_def step_def mtf2_def swap_def OPT2x)
                  also have "\<dots> \<le> 1 +  T\<^sub>p_opt [y, x] (rest2)" apply(simp)
                    apply(rule less(1))
                      apply(simp add: less(2) Cons1 Cons)
                      using v less(3) by(auto)
                  also

                  have "\<dots> \<le> T\<^sub>p [x, y] (y # y # rest2) Strat"
                  proof (cases "?L2 = [y,x]")
                    case True
                    have 2: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p [y,x] rest2 (tl (tl Strat)) \<ge> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p_opt [y,x] rest2" apply(simp)
                            unfolding T_opt_def apply(rule cInf_lower)
                            apply(simp) apply(rule exI[where x="tl (tl Strat)"]) by (auto simp: lenStrat)
                    have 3: "t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))
                            + T\<^sub>p_opt [y,x] rest2 \<ge> 1 + T\<^sub>p_opt [y,x] rest2" apply(simp)
                            proof -
                              have "t\<^sub>p [x, y] y (hd Strat) \<ge> 1"
                              unfolding t\<^sub>p_def apply(simp add: split_def)
                              apply(cases "snd (hd Strat)") by (simp_all add: less(3))
                              then show "Suc 0 \<le> t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat))" by auto
                            qed
                    from 1 2 3 True show ?thesis by auto 
                  next
                    case False 
                    note L2F=this
                    have L1: "?L1 \<in> {[x, y], [y, x]}" apply(rule stepxy) by simp_all
                    have "?L2 \<in> {[x, y], [y, x]}" apply(rule stepxy) using L1 by simp_all
                    with False have 2: "?L2 = [x,y]" by auto

                    have k: "T\<^sub>p [x, y] (y # y # rest2) Strat
                        =   t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat)) +
                            T\<^sub>p [x,y] rest2 (tl (tl Strat))" using 1 2 by auto

                    have l: "t\<^sub>p [x, y] y (hd Strat) > 0"
                        using less(3) unfolding t\<^sub>p_def apply(cases "snd (hd Strat) = []")
                          by (simp_all add: split_def)

                    have r: "T\<^sub>p [x, y] (y # y # rest2) Strat \<ge> 2 + T\<^sub>p [x,y] rest2 (tl (tl Strat))"
                    proof (cases "?L1 = [y,x]")  
                      case False
                      from L1 False have "?L1 = [x,y]" by auto
                      note T=this
                      then have "t\<^sub>p ?L1 y (hd (tl Strat)) > 0" unfolding T
                      unfolding t\<^sub>p_def apply(simp add: split_def)
                        apply(cases "snd (hd (tl Strat)) = []")
                          using \<open>x \<noteq> y\<close> by auto
                      with l k show ?thesis by auto
                    next

                      case True
                      note T=this
                          
                        have "t\<^sub>p ?L1 y (hd (tl Strat)) > 0" unfolding T
                        proof(cases "snd (hd (tl Strat)) = []")
                          case True
                          have "?L2 = [y,x]" unfolding T  apply(simp add: split_def step_def) 
                          unfolding True mtf2_def by(simp)
                          with L2F have "False" by auto
                          then show "0 < t\<^sub>p [y, x] y (hd (tl Strat))" ..
                        next
                          case False
                          then show "0 < t\<^sub>p [y, x] y (hd (tl Strat))"
                            unfolding t\<^sub>p_def by(simp add: split_def)
                        qed                          
                      with l have " t\<^sub>p [x, y] y (hd Strat) + t\<^sub>p ?L1 y (hd (tl Strat)) \<ge> 2" by auto
                      with k show ?thesis by auto
                    
                    qed
                    have t: "T\<^sub>p [x, y] rest2 (tl (tl Strat)) \<ge> T\<^sub>p_opt [x, y] rest2" 
                      unfolding T_opt_def apply(rule cInf_lower)
                      apply(auto) apply(rule exI[where x="(tl (tl Strat))"]) by(simp add: lenStrat)
                    show ?thesis
                    proof -
                      have "1 + T\<^sub>p_opt [y, x] rest2 \<le> 2 + T\<^sub>p_opt [x, y] rest2"
                      using  swapOpt by auto
                      also have "\<dots> \<le> 2 + T\<^sub>p [x, y] rest2 (tl (tl Strat))" using t by auto
                      also have "\<dots> \<le> T\<^sub>p [x, y] (y # y # rest2) Strat" using r by auto
                      finally show ?thesis .
                    qed
                      
                  qed
                  also have "\<dots> = el" using Strat by auto
                  finally show "T\<^sub>p [x, y] (y # y # rest2) (OPT2 (y # y # rest2) [x, y]) \<le> el" .
                qed
          qed
        qed
     qed
  qed (simp add: T_opt_def)
qed


lemma OPT2_is_ub: "set qs \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) \<ge> T\<^sub>p_opt [x,y] qs"
  unfolding T_opt_def apply(rule cInf_lower)
            apply(simp) apply(rule exI[where x="(OPT2 qs [x, y])"])
            by (auto simp add: OPT2_length)



lemma OPT2_is_opt: "set qs \<subseteq> {x,y} \<Longrightarrow> x\<noteq>y \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = T\<^sub>p_opt [x,y] qs"
by (simp add: OPT2_is_lb OPT2_is_ub antisym)


subsection "Performance on the four phase forms"

lemma OPT2_A: assumes "x \<noteq> y" "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
  shows "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = 1"
proof -
  from assms(2) obtain u v where qs: "qs=u@v" and u: "u=[x] \<or> u=[]" and v: "v = [y,y]" by (auto simp: conc_def)
  from u have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  have ende: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1" unfolding v using assms(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)

  from pref1 ende qs show ?thesis by auto
qed
  

lemma OPT2_A': assumes "x \<noteq> y" "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
  shows "real (T\<^sub>p [x,y] qs (OPT2 qs [x,y])) = 1"
using OPT2_A[OF assms] by simp


lemma OPT2_B: assumes "x \<noteq> y" "qs=u@v" "u=[] \<or> u=[x]" "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
  shows "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)"
proof -
  from assms(3) have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  from assms(4) obtain a w where v: "v=a@w" and "a\<in>lang (Times (Atom y) (Atom x))" and w: "w\<in>lang (seq[Star(Times (Atom y) (Atom x)), Atom y, Atom y])" by(auto)
  from this(2) have aa: "a=[y,x]" by(simp add: conc_def)

  from assms(1) this v have pref2: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1 + T\<^sub>p [x,y] w (OPT2 w [x,y])"
   by(simp add: t\<^sub>p_def step_def OPT2x)

  from w obtain c d where w2: "w=c@d" and c: "c \<in> lang (Star (Times (Atom y) (Atom x)))" and d: "d \<in> lang (Times (Atom y) (Atom y))" by auto
  then have dd: "d=[y,y]" by auto

  from c[simplified] have star: "T\<^sub>p [x,y] (c@d) (OPT2 (c@d) [x,y]) = (length c div 2) +  T\<^sub>p [x,y] d (OPT2 d [x,y])"
    proof(induct c rule: star_induct)
      case (append r s)       
      then have r: "r=[y,x]" by auto
      then have "T\<^sub>p [x, y] ((r @ s) @ d) (OPT2 ((r @ s) @ d) [x, y]) = T\<^sub>p [x, y] ([y,x] @ (s @ d)) (OPT2 ([y,x] @ (s @ d)) [x, y])" by simp
      also have "\<dots> = 1 + T\<^sub>p [x, y] (s @ d) (OPT2 (s @ d) [x, y])"
        using assms(1) by(simp add: t\<^sub>p_def step_def OPT2x)
      also have "\<dots> =  1 + length s div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using append by simp
      also have "\<dots> =  length (r @ s) div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using r by auto
      finally show ?case .
    qed simp

  have ende: "T\<^sub>p [x,y] d (OPT2 d [x,y]) = 1" unfolding dd using assms(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)
  
  have vv: "v = [y,x]@c@[y,y]" using w2 dd v aa by auto

  from pref1 pref2 star w2 ende have
    "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 1 + length c div 2 + 1" unfolding assms(2) by auto
  also have "\<dots> = (length v div 2)" using vv by auto
  finally show ?thesis .
qed

lemma OPT2_B1: assumes "x \<noteq> y" "qs \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
  shows "real (T\<^sub>p [x,y] qs (OPT2 qs [x,y])) = length qs / 2"
proof -
  from assms(2) have qs: "qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
    by(simp add: conc_assoc)
  have "(length qs) mod 2 = 0"
  proof -
    from assms(2) have "qs \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}" by (simp add: conc_assoc)
    then obtain p q r where pqr: "qs=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length qs = 4+length q" by auto
    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed
  with OPT2_B[where u="[]", OF assms(1) _ _ qs] show ?thesis by auto
qed  
  
lemma OPT2_B2: assumes "x \<noteq> y" "qs \<in> lang (seq[Atom x, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom y, Atom y])"
  shows "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = ((length qs - 1) / 2)"
proof -
  from assms(2) obtain v where
      qsv: "qs = [x]@v" and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x)), Atom y, Atom y])" by (auto simp add: conc_def)
  have "(length v) mod 2 = 0"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}" by (simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[y,y]" by(auto simp add: conc_def)
    with pqr have a: "length v = 4+length q" by auto
    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed
  with OPT2_B[where u="[x]", OF assms(1) qsv _ vv] qsv show ?thesis by(auto)
qed 

lemma OPT2_C: assumes "x \<noteq> y" "qs=u@v" "u=[] \<or> u=[x]" 
  and "v \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
  shows "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)"
proof -
  from assms(3) have pref1: "T\<^sub>p [x,y] (u@v) (OPT2 (u@v) [x,y]) = T\<^sub>p [x,y] v (OPT2 v [x,y])"
    apply(cases "u=[]")
      apply(simp)
      by(simp add: OPT2x t\<^sub>p_def step_def)

  from assms(4) obtain a w where v: "v=a@w" and aa: "a=[y,x]" and w: "w\<in>lang (seq[Star(Times (Atom y) (Atom x)), Atom x])" by(auto simp: conc_def)

  from assms(1) this v have pref2: "T\<^sub>p [x,y] v (OPT2 v [x,y]) = 1 + T\<^sub>p [x,y] w (OPT2 w [x,y])"
   by(simp add: t\<^sub>p_def step_def OPT2x)

  from w obtain c d where w2: "w=c@d" and c: "c \<in> lang (Star (Times (Atom y) (Atom x)))" and d: "d \<in> lang (Atom x)" by auto
  then have dd: "d=[x]" by auto

  from c[simplified] have star: "T\<^sub>p [x,y] (c@d) (OPT2 (c@d) [x,y]) = (length c div 2) +  T\<^sub>p [x,y] d (OPT2 d [x,y]) \<and> (length c) mod 2 = 0"
    proof(induct c rule: star_induct)
      case (append r s)
      from append have mod: "length s mod 2 = 0" by simp
      from append have r: "r=[y,x]" by auto
      then have "T\<^sub>p [x, y] ((r @ s) @ d) (OPT2 ((r @ s) @ d) [x, y]) = T\<^sub>p [x, y] ([y,x] @ (s @ d)) (OPT2 ([y,x] @ (s @ d)) [x, y])" by simp
      also have "\<dots> = 1 + T\<^sub>p [x, y] (s @ d) (OPT2 (s @ d) [x, y])"
        using assms(1) by(simp add: t\<^sub>p_def step_def OPT2x)
      also have "\<dots> =  1 + length s div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using append by simp
      also have "\<dots> =  length (r @ s) div 2 + T\<^sub>p [x, y] d (OPT2 d [x, y])" using r by auto
      finally show ?case by(simp add: mod r)
    qed simp

  have ende: "T\<^sub>p [x,y] d (OPT2 d [x,y]) = 0" unfolding dd using assms(1) by(simp add: mtf2_def swap_def t\<^sub>p_def step_def)
  
  have vv: "v = [y,x]@c@[x]" using w2 dd v aa by auto

  from pref1 pref2 star w2 ende have
    "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = 1 + length c div 2" unfolding assms(2) by auto
  also have "\<dots> = (length v div 2)" using vv star by auto
  finally show ?thesis .
qed

lemma OPT2_C1: assumes "x \<noteq> y" "qs \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
  shows "real (T\<^sub>p [x,y] qs (OPT2 qs [x,y])) = (length qs - 1) / 2"
proof -
  from assms(2) have qs: "qs \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
    by(simp add: conc_assoc)
  have "(length qs) mod 2 = 1"
  proof -
    from assms(2) have "qs \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}" by (simp add: conc_assoc)
    then obtain p q r where pqr: "qs=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[x]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length qs = 3+length q" by auto
    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed
  with OPT2_C[where u="[]", OF assms(1) _ _ qs] show ?thesis apply auto
      by (metis minus_mod_eq_div_mult [symmetric] of_nat_mult of_nat_numeral) 
qed  
  
lemma OPT2_C2: assumes "x \<noteq> y" "qs \<in> lang (seq[Atom x, Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])"
  shows "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = ((length qs - 2) / 2)"
proof -
  from assms(2) obtain v where
      qsv: "qs = [x]@v" and vv: "v \<in> lang (seq[Atom y, Atom x, Star(Times (Atom y) (Atom x)), Atom x])" by (auto simp add: conc_def)
  have "(length v) mod 2 = 1"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}" by (simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[x]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[x]" by(auto simp add: conc_def)
    with pqr have a: "length v = 3+length q" by auto
    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed
  with OPT2_C[where u="[x]", OF assms(1) qsv _ vv] qsv show ?thesis apply(auto)
      by (metis minus_mod_eq_div_mult [symmetric] of_nat_mult of_nat_numeral)     
qed 



lemma OPT2_ub: "set qs \<subseteq> {x,y} \<Longrightarrow> T\<^sub>p [x,y] qs (OPT2 qs [x,y]) \<le> length qs"
proof(induct qs arbitrary: x y)
  case (Cons q qs)
  then have "set qs \<subseteq> {x,y}" "q\<in>{x,y}" by auto
  note Cons1=Cons this
  show ?case
  proof (cases qs)
    case Nil
    with Cons1 show "T\<^sub>p [x,y] (q # qs) (OPT2 (q # qs) [x,y]) \<le> length (q # qs)"
        apply(simp add: t\<^sub>p_def) by blast
  next
    case (Cons q' qs')
    with Cons1 have "q'\<in>{x,y}" by auto
    note Cons=Cons this

    from Cons1 Cons have T: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<le> length qs"
                            "T\<^sub>p [y, x] qs (OPT2 qs [y, x]) \<le> length qs" by auto
    show "T\<^sub>p [x,y] (q # qs) (OPT2 (q # qs) [x,y]) \<le> length (q # qs)"
          unfolding Cons apply(simp only: OPT2.simps)
          apply(split if_splits(1))
            apply(safe)
            proof (goal_cases)
              case 1
              have "T\<^sub>p [x, y] (x # q' # qs') ((0, []) # OPT2 (q' # qs') [x, y])
                      = t\<^sub>p [x, y] x (0,[]) + T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
                        by(simp add: step_def Cons)
              also have "\<dots> \<le> t\<^sub>p [x, y] x (0,[]) + length qs" using T by auto
              also have "\<dots> \<le> length (x # q' # qs')" using Cons by(simp add: t\<^sub>p_def)
              finally show ?case .
            next
              case 2
              with Cons1 Cons show ?case
                apply(split if_splits(1))
                apply(safe)
                proof (goal_cases)
                  case 1
                  then have "T\<^sub>p [x, y] (y # x # qs') ((0, []) # OPT2 (x # qs') [x, y])
                          = t\<^sub>p [x, y] y (0,[]) + T\<^sub>p [x, y] qs (OPT2 qs [x, y])"
                            by(simp add: step_def)
                  also have "\<dots> \<le> t\<^sub>p [x, y] y (0,[]) + length qs" using T by auto
                  also have "\<dots> \<le> length (y # x # qs')" using Cons by(simp add: t\<^sub>p_def)
                  finally show ?case .
                next
                  case 2
                  then have "T\<^sub>p [x, y] (y # y # qs') ((1, []) # OPT2 (y # qs') [y, x])
                          = t\<^sub>p [x, y] y (1,[]) + T\<^sub>p [y, x] qs (OPT2 qs [y, x])"
                            by(simp add: step_def mtf2_def swap_def)
                  also have "\<dots> \<le> t\<^sub>p [x, y] y (1,[]) + length qs" using T by auto
                  also have "\<dots> \<le> length (y # y # qs')" using Cons by(simp add: t\<^sub>p_def)
                  finally show ?case .
                qed
           qed
  qed
qed simp 

lemma OPT2_padded: "R\<in>{[x,y],[y,x]} \<Longrightarrow> set qs \<subseteq> {x,y} 
      \<Longrightarrow>  T\<^sub>p R (qs@[x,x]) (OPT2 (qs@[x,x]) R)
              \<le> T\<^sub>p R (qs@[x]) (OPT2 (qs@[x]) R) + 1"
apply(induct qs arbitrary: R)
  apply(simp)
    apply(case_tac "R=[x,y]")
      apply(simp add: step_def t\<^sub>p_def )
      apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
  proof (goal_cases)
    case (1 a qs R)
    then have a: "a \<in> {x,y}" by auto 
    with 1 show ?case
      apply(cases qs)
        apply(cases "a=x")
          apply(cases "R=[x,y]")
            apply(simp add: step_def t\<^sub>p_def)
            apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
          apply(cases "R=[x,y]")
            apply(simp add: step_def t\<^sub>p_def)
            apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
      proof (goal_cases)
        case (1 p ps)
        show ?case
          apply(cases "a=x")
            apply(cases "R=[x,y]")
              apply(simp add: OPT2x step_def) using 1 apply(simp)
              using 1(2) apply(simp)
                apply(cases qs)
                  apply(simp add: step_def mtf2_def swap_def t\<^sub>p_def)
                  using 1 by(auto simp add: swap_def mtf2_def step_def)
       qed
qed 


lemma  OPT2_split11:
  assumes xy: "x\<noteq>y"
  shows "R\<in>{[x,y],[y,x]} \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow> OPT2 (xs@[x,x]@ys) R = OPT2 (xs@[x,x]) R @ OPT2 ys [x,y]"
proof (induct xs arbitrary: R)
  case Nil
  then show ?case
  apply(simp)
  apply(cases ys)
    apply(simp)
    apply(cases "R=[x,y]") 
      apply(simp)
      by(simp)
next
  case (Cons a as)
  note iH=this
  then have AS: "set as \<subseteq> {x,y}" and A: "a \<in> {x,y}" by auto
  note iH=Cons(1)[where R="[y,x]", simplified, OF AS Cons(4)]
  note iH'=Cons(1)[where R="[x,y]", simplified, OF AS Cons(4)]
  show ?case
  proof (cases "R=[x,y]")
    case True
    note R=this
    from iH iH' show ?thesis
    apply(cases "a=x")
      apply(simp add: R OPT2x)
      using A apply(simp)
      apply(cases as)
        apply(simp add: R)
        using AS apply(simp)
        apply(case_tac "aa=x")
          by(simp_all add: R)
  next
    case False
    with Cons(2) have R: "R=[y,x]" by auto
    from iH iH' show ?thesis
    apply(cases "a=y")
      apply(simp add: R OPT2x)
      using A apply(simp)
      apply(cases as)
        apply(simp add: R) 
        apply(case_tac "aa=y")
          by (simp_all add: R)
   qed  
qed  
 
subsection "The function steps" 
 
 
lemma steps_append: "length qs = length as \<Longrightarrow> steps s (qs@[q]) (as@[a]) = step (steps s qs as) q a"
apply(induct qs as arbitrary: s rule: list_induct2) by simp_all
 
end
