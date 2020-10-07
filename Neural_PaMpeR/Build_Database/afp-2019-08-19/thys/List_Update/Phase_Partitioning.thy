(*  Title:       Phase Partitioning
    Author:      Max Haslbeck
*)

section "Phase Partitioning"

theory Phase_Partitioning
imports OPT2
begin


subsection "Definition of Phases"

definition "other a x y = (if a=x then y else x)"


definition Lxx where
  "Lxx (x::nat) y = lang (L_lasthasxx x y)"

lemma Lxx_not_nullable: "[] \<notin> Lxx x y"
unfolding Lxx_def L_lasthasxx_def by simp

(* lemma set_Lxx: "xs \<in> Lxx x y \<Longrightarrow> set xs \<subseteq> {x,y}"
unfolding Lxx_def L_lasthasxx_def apply(simp add: star_def) sle dgehammer *)


lemma Lxx_ends_in_two_equal: "xs \<in> Lxx x y \<Longrightarrow> \<exists>pref e. xs = pref @ [e,e]"
by(auto simp: conc_def Lxx_def L_lasthasxx_def) 


lemma "Lxx x y = Lxx y x" unfolding Lxx_def by(rule lastxx_com)

definition "hideit x y = (Plus rexp.One (nodouble x y))"

lemma Lxx_othercase: "set qs \<subseteq> {x,y} \<Longrightarrow> \<not> (\<exists>xs ys. qs = xs @ ys \<and> xs \<in> Lxx x y) \<Longrightarrow> qs \<in> lang (hideit x y)"
proof -
  assume "set qs \<subseteq> {x,y}"
  then have "qs \<in> lang (myUNIV x y)" using myUNIV_alle[of x y] by blast
  then have "qs \<in> star (lang (L_lasthasxx x y)) @@  lang (hideit x y)" unfolding hideit_def
    by(auto simp add: myUNIV_char)
  then have qs: "qs \<in> star (Lxx x y) @@  lang (hideit x y)" by(simp add: Lxx_def)
  assume notpos: "\<not> (\<exists>xs ys. qs = xs @ ys \<and> xs \<in> Lxx x y)"
  show "qs \<in> lang (hideit x y)"
  proof -
    from qs obtain A B where qsAB: "qs=A@B" and A: "A\<in>star (Lxx x y)" and B: "B\<in>lang (hideit x y)" by auto
    with notpos have notin: "A \<notin> (Lxx x y)" by blast
    
    from A have 1: "A = [] \<or> A \<in> (Lxx x y) @@ star (Lxx x y)" using Regular_Set.star_unfold_left by auto
    have 2: "A \<notin> (Lxx x y) @@ star (Lxx x y)"
    proof (rule ccontr)
      assume "\<not> A \<notin> Lxx x y @@ star (Lxx x y)"
      then have " A \<in> Lxx x y @@ star (Lxx x y)" by auto
      then obtain A1 A2 where "A=A1@A2" and A1: "A1\<in>(Lxx x y)" and "A2\<in> star (Lxx x y)" by auto
      with qsAB have "qs=A1@(A2@B)" "A1\<in>(Lxx x y)" by auto
      with notpos have "A1 \<notin> (Lxx x y)" by blast
      with A1 show "False" by auto
    qed
    from 1 2 have "A=[]" by auto
    with qsAB have "qs=B" by auto
    with B show ?thesis by simp
  qed
qed


fun pad where "pad xs x y = (if xs=[] then [x,x] else 
                                    (if last xs = x then xs @ [x] else xs @ [y]))"

lemma pad_adds2: "qs \<noteq> [] \<Longrightarrow> set qs \<subseteq> {x,y} \<Longrightarrow> pad qs x y = qs @ [last qs]"
apply(auto) by (metis insertE insert_absorb insert_not_empty last_in_set subset_iff) 


lemma nodouble_padded: "qs \<noteq> [] \<Longrightarrow> qs \<in> lang (nodouble x y) \<Longrightarrow> pad qs x y \<in> Lxx x y"
proof -
  assume nn: "qs \<noteq> []"
  assume "qs \<in> lang (nodouble x y)"
  then have a: "qs \<in> lang         (seq
          [Plus (Atom x) rexp.One,
           Star (Times (Atom y) (Atom x)),
           Atom y]) \<or> qs \<in> lang
        (seq
          [Plus (Atom y) rexp.One,
           Star (Times (Atom x) (Atom y)),
           Atom x])"  unfolding nodouble_def by auto


  show ?thesis
  proof (cases "qs \<in> lang (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)), Atom y])")
    case True
    then have "qs \<in> lang (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x))]) @@ {[y]}"
      by(simp add: conc_assoc)
    then have "last qs = y" by auto
    with nn have p: "pad qs x y = qs @ [y]" by auto
    have A: "pad qs x y \<in> lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y]) @@ {[y]}" unfolding p
             apply(simp)
             apply(rule concI)
              using True by auto
    have B: "lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y]) @@ {[y]} = lang  (seq [Plus (Atom x) One, Star (Times (Atom y) (Atom x)),
             Atom y, Atom y])" by (simp add: conc_assoc)
    show "pad qs x y \<in> Lxx x y" unfolding Lxx_def L_lasthasxx_def 
      using B A by auto
  next
    case False
    with a have T: "qs \<in> lang (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)), Atom x])" by auto

    then have "qs \<in> lang (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y))]) @@ {[x]}"
      by(simp add: conc_assoc)
    then have "last qs = x" by auto
    with nn have p: "pad qs x y = qs @ [x]" by auto
    have A: "pad qs x y \<in> lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x]) @@ {[x]}" unfolding p
             apply(simp)
             apply(rule concI)
              using T by auto
    have B: "lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x]) @@ {[x]} = lang  (seq [Plus (Atom y) One, Star (Times (Atom x) (Atom y)),
             Atom x, Atom x])" by (simp add: conc_assoc)
    show "pad qs x y \<in> Lxx x y" unfolding Lxx_def L_lasthasxx_def 
      using B A by auto
 qed
qed

thm UnE
lemma "c \<in> A \<union> B \<Longrightarrow> P"
  apply(erule UnE) oops

lemma LxxE: "qs \<in> Lxx x y
    \<Longrightarrow> (qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> P x y qs"
unfolding Lxx_def lastxx_is_4cases[symmetric] L_4cases_def apply(simp only: verund.simps lang.simps)
using UnE by blast

thm UnE LxxE

lemma "qs \<in> Lxx x y \<Longrightarrow> P"
apply(erule LxxE) oops

lemma LxxI: "(qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom y]) \<Longrightarrow> P x y qs)
    \<Longrightarrow> (qs \<in> Lxx x y \<Longrightarrow> P x y qs)"
unfolding Lxx_def lastxx_is_4cases[symmetric] L_4cases_def apply(simp only: verund.simps lang.simps)
  by blast


lemma Lxx1: "xs \<in> Lxx x y \<Longrightarrow> length xs \<ge> 2"
  apply(rule LxxI[where P="(\<lambda>x y qs. length qs \<ge> 2)"])
  apply(auto) by(auto simp: conc_def)

subsection "OPT2 Splitting"
         

lemma ayay: "length qs = length as \<Longrightarrow> T\<^sub>p s (qs@[q]) (as@[a]) = T\<^sub>p s qs as + t\<^sub>p (steps s qs as) q a"
apply(induct qs as arbitrary: s rule: list_induct2) by simp_all

lemma tlofOPT2: "Q \<in> {x,y} \<Longrightarrow> set QS \<subseteq> {x,y} \<Longrightarrow> R \<in> {[x, y], [y, x]} \<Longrightarrow> tl (OPT2 ((Q # QS) @ [x, x]) R) =
    OPT2 (QS @ [x, x]) (step R Q (hd (OPT2 ((Q # QS) @ [x, x]) R)))"
      apply(cases "Q=x")
        apply(cases "R=[x,y]")
          apply(simp add: OPT2x step_def)
          apply(simp)
            apply(cases QS)
                apply(simp add: step_def mtf2_def swap_def)
                apply(simp add: step_def mtf2_def swap_def)
        apply(cases "R=[x,y]")
          apply(simp)
            apply(cases QS)
                apply(simp add: step_def mtf2_def swap_def)
                apply(simp add: step_def mtf2_def swap_def)
          by(simp add: OPT2x step_def)


lemma T\<^sub>p_split: "length qs1=length as1 \<Longrightarrow> T\<^sub>p s (qs1@qs2) (as1@as2) = T\<^sub>p s qs1 as1 + T\<^sub>p (steps s qs1 as1) qs2 as2"
apply(induct qs1 as1 arbitrary: s rule: list_induct2) by(simp_all)
 
lemma T\<^sub>p_spliting: "x\<noteq>y \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow>
      R \<in> {[x,y],[y,x]} \<Longrightarrow>
      T\<^sub>p R (xs@[x,x]) (OPT2 (xs@[x,x]) R) + T\<^sub>p [x,y] ys (OPT2 ys [x,y])
      = T\<^sub>p R (xs@[x,x]@ys) (OPT2 (xs@[x,x]@ys) R)"
proof -
  assume nxy: "x\<noteq>y"
  assume XSxy: "set xs \<subseteq> {x,y}"
  assume YSxy: "set ys \<subseteq> {x,y}"
  assume R: "R \<in> {[x,y],[y,x]}"
  {
    fix R
    assume XSxy: "set xs \<subseteq> {x,y}"
    have "R\<in>{[x,y],[y,x]} \<Longrightarrow> set xs \<subseteq> {x,y}  \<Longrightarrow> steps R (xs@[x,x]) (OPT2 (xs@[x,x]) R) = [x,y]"
    proof(induct xs arbitrary: R)
      case Nil
      then show ?case
        apply(cases "R=[x,y]")
(* FIXME why is simp_all needed? *)
          apply simp_all apply(simp add: step_def)
          by(simp add: step_def mtf2_def swap_def)
    next
      case (Cons Q QS)
      let ?R'="(step R Q (hd (OPT2 ((Q # QS) @ [x, x]) R)))"

      have a: "Q \<in> {x,y}"  and b: "set QS \<subseteq> {x,y}" using Cons by auto 
      have t: "?R' \<in> {[x,y],[y,x]}"
        apply(rule stepxy) using nxy Cons by auto
      then have "length (OPT2 (QS @ [x, x]) ?R') > 0" 
        apply(cases "?R' = [x,y]") by(simp_all add: OPT2_length)
      then have "OPT2 (QS @ [x, x]) ?R' \<noteq> []" by auto
      then have hdtl: "OPT2 (QS @ [x, x]) ?R' = hd (OPT2 (QS @ [x, x]) ?R') # tl (OPT2 (QS @ [x, x]) ?R')" 
         by auto

      have maa: "(tl (OPT2 ((Q # QS) @ [x, x]) R)) = OPT2 (QS @ [x, x]) ?R' "
        using tlofOPT2[OF a b Cons(2)] by auto

      
      from Cons(2) have "length (OPT2 ((Q # QS) @ [x, x]) R) > 0" 
        apply(cases "R = [x,y]") by(simp_all add: OPT2_length)
      then have nempty: "OPT2 ((Q # QS) @ [x, x]) R \<noteq> []" by auto
      then have "steps R ((Q # QS) @ [x, x]) (OPT2 ((Q # QS) @ [x, x]) R)
        = steps R ((Q # QS) @ [x, x]) (hd(OPT2 ((Q # QS) @ [x, x]) R) #  tl(OPT2 ((Q # QS) @ [x, x]) R))"
          by(simp)
      also have "\<dots>    
        = steps ?R' (QS @ [x,x]) (tl (OPT2 ((Q # QS) @ [x, x]) R))"
          unfolding maa by auto
      also have "\<dots> = steps ?R' (QS @ [x,x]) (OPT2 (QS @ [x, x]) ?R')" using maa by auto
      also with Cons(1)[OF t b] have "\<dots> = [x,y]" by auto
      
        
      finally show ?case .
    qed
  } note aa=this

    from aa XSxy R have ll: "steps R (xs@[x,x]) (OPT2 (xs@[x,x]) R)
      = [x,y]" by auto

  have uer: " length (xs @ [x, x]) = length (OPT2 (xs @ [x, x]) R)"
    using R  by (auto simp: OPT2_length)

  have "OPT2 (xs @ [x, x] @ ys) R = OPT2 (xs @ [x, x]) R @ OPT2 ys [x, y]" 
    apply(rule OPT2_split11)
      using nxy XSxy YSxy R by auto


  then have "T\<^sub>p R (xs@[x,x]@ys) (OPT2 (xs@[x,x]@ys) R)
        = T\<^sub>p R ((xs@[x,x])@ys) (OPT2 (xs @ [x, x]) R @ OPT2 ys [x, y])"  by auto
  also have "\<dots> = T\<^sub>p R (xs@[x,x]) (OPT2 (xs @ [x, x]) R)
                + T\<^sub>p [x,y] ys (OPT2 ys [x, y])"
                  using T\<^sub>p_split[of "xs@[x,x]" "OPT2 (xs @ [x, x]) R" R ys "OPT2 ys [x, y]", OF uer, unfolded ll] 
                by auto
  finally show ?thesis by simp
qed


lemma OPTauseinander: "x\<noteq>y \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> set ys \<subseteq> {x,y} \<Longrightarrow>
      LTS \<in> {[x,y],[y,x]} \<Longrightarrow> hd LTS = last xs \<Longrightarrow>
     xs = (pref @ [hd LTS, hd LTS]) \<Longrightarrow> 
      T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p LTS ys (OPT2 ys LTS)
      = T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])"
proof -
  assume nxy: "x\<noteq>y"
  assume xsxy: "set xs \<subseteq> {x,y}"
  assume ysxy: "set ys \<subseteq> {x,y}"
  assume L: "LTS \<in> {[x,y],[y,x]}"
  assume "hd LTS = last xs"
  assume prefix: "xs = (pref @ [hd LTS, hd LTS])"
  show ?thesis
    proof (cases "LTS = [x,y]")
      case True
      show ?thesis unfolding True prefix
        apply(simp)
        apply(rule T\<^sub>p_spliting[simplified])
          using nxy xsxy ysxy prefix by auto
    next
      case False
      with L have TT: "LTS = [y,x]" by auto
      show ?thesis unfolding TT prefix
        apply(simp)
        apply(rule T\<^sub>p_spliting[simplified])
          using nxy xsxy ysxy prefix by auto
   qed
qed


subsection "Phase Partitioning lemma"


theorem Phase_partitioning_general: 
  fixes P :: "(nat state * 'is) pmf \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
      and A :: "(nat state,'is,nat,answer) alg_on_rand"
  assumes xny: "(x0::nat) \<noteq> y0" 
    and cpos: "(c::real)\<ge>0"
    and static: "set \<sigma> \<subseteq> {x0,y0}" 
    and initial: "P (map_pmf (%is. ([x0,y0],is)) (fst A [x0,y0])) x0 [x0,y0]"
    and D: "\<And>a b \<sigma> s.  \<sigma> \<in> Lxx a b \<Longrightarrow> a\<noteq>b \<Longrightarrow> {a,b}={x0,y0} \<Longrightarrow> P s a [x0,y0]  \<Longrightarrow> set \<sigma> \<subseteq> {a,b}
          \<Longrightarrow> T_on_rand' A s \<sigma> \<le> c * T\<^sub>p [a,b] \<sigma> (OPT2 \<sigma> [a,b])  \<and> P (config'_rand A s \<sigma>) (last \<sigma>) [x0,y0]"
  shows "T\<^sub>p_on_rand A [x0,y0] \<sigma>  \<le> c * T\<^sub>p_opt [x0,y0] \<sigma> + c"
proof -
  
 {
   fix x y s
 have "x \<noteq> y \<Longrightarrow> P s x [x0,y0] \<Longrightarrow> set \<sigma> \<subseteq> {x,y} \<Longrightarrow> {x,y}={x0,y0} \<Longrightarrow> T_on_rand' A s \<sigma> \<le> c * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + c"
 proof (induction "length \<sigma>" arbitrary: \<sigma> x y s rule: less_induct)
  case (less \<sigma>) 

  show ?case
  proof (cases "\<exists>xs ys. \<sigma>=xs@ys \<and> xs \<in> Lxx x y")
    case True 

    then obtain xs ys where qs: "\<sigma>=xs@ys" and xsLxx: "xs \<in> Lxx x y" by auto

    with Lxx1 have len: "length ys < length \<sigma>" by fastforce
    from qs(1) less(4) have ysxy: "set ys \<subseteq> {x,y}" by auto

    have xsset: "set xs \<subseteq> {x, y}" using less(4) qs by auto
    from xsLxx Lxx1 have lxsgt1: "length xs \<ge> 2" by auto
    then have xs_not_Nil: "xs \<noteq> []" by auto

    from D[OF xsLxx less(2) less(5) less(3) xsset] 
      have D1: "T_on_rand' A s xs \<le> c * T\<^sub>p [x, y] xs (OPT2 xs [x, y])" 
         and inv: "P (config'_rand A s xs) (last xs) [x0, y0]" by auto
 

    from xsLxx Lxx_ends_in_two_equal obtain pref e where "xs = pref @ [e,e]" by metis
    then have endswithsame: "xs = pref @ [last xs, last xs]" by auto 

    let ?c' = "[last xs, other (last xs) x y]" 

    have setys: "set ys \<subseteq> {x,y}" using qs less by auto 
    have setxs: "set xs \<subseteq> {x,y}" using qs less by auto 
    have lxs: "last xs \<in> set xs" using xs_not_Nil by auto
    from lxs setxs have lxsxy: "last xs \<in> {x,y}" by auto 
     from lxs setxs have otherxy: "other (last xs) x y \<in> {x,y}" by (simp add: other_def)
    from less(2) have other_diff: "last xs \<noteq> other (last xs) x y" by(simp add: other_def)
 
    have lo: "{last xs, other (last xs) x y} = {x0, y0}"
      using lxsxy otherxy other_diff less(5) by force

    have nextstate: "{[last xs, other (last xs) x y], [other (last xs) x y, last xs]}
            = { [x,y],[y,x]}" using lxsxy otherxy other_diff by fastforce
    have setys': "set ys \<subseteq> {last xs, other (last xs) x y}"
            using setys lxsxy otherxy other_diff by fastforce
   
    have c: "T_on_rand' A (config'_rand A s xs) ys
        \<le> c * T\<^sub>p ?c' ys (OPT2 ys ?c') + c"       
            apply(rule less(1))
              apply(fact len)
              apply(fact other_diff) 
              apply(fact inv) 
              apply(fact setys')
              by(fact lo)
 

    have well: "T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')
        = T\<^sub>p [x, y] (xs @ ys) (OPT2 (xs @ ys) [x, y])"
          apply(rule OPTauseinander[where pref=pref])
            apply(fact)+
            using lxsxy other_diff otherxy apply(fastforce)
            apply(simp)
            using endswithsame by simp  
      
    have E0: "T_on_rand' A s \<sigma>
          =  T_on_rand' A s (xs@ys)" using qs by auto
     also have E1: "\<dots> = T_on_rand' A s xs + T_on_rand' A (config'_rand A s xs) ys"
              by (rule T_on_rand'_append)
    also have E2: "\<dots> \<le> T_on_rand' A s xs + c * T\<^sub>p ?c' ys (OPT2 ys ?c') + c"
        using c by simp
    also have E3: "\<dots> \<le> c * T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + c * T\<^sub>p ?c' ys (OPT2 ys ?c') + c"
        using D1 by simp        
    also have "\<dots> = c * (T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')) + c"
        using cpos apply(auto) by algebra
    also have  "\<dots> = c * (T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])) + c"
      using well by auto 
    also have E4: "\<dots> = c * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])) + c"
        using qs by auto
    finally show ?thesis .
  next
    case False
    note f1=this
    from Lxx_othercase[OF less(4) this, unfolded hideit_def] have
        nodouble: "\<sigma> = [] \<or> \<sigma> \<in> lang (nodouble x y)" by  auto
    show ?thesis
    proof (cases "\<sigma> = []")
      case True
      then show ?thesis using cpos  by simp
    next
      case False
      (* with padding *)
      from False nodouble have qsnodouble: "\<sigma> \<in> lang (nodouble x y)" by auto
      let ?padded = "pad \<sigma> x y"
      
      have padset: "set ?padded \<subseteq> {x, y}" using less(4) by(simp)

      from False pad_adds2[of \<sigma> x y] less(4) obtain addum where ui: "pad \<sigma> x y = \<sigma> @ [last \<sigma>]" by auto
      from nodouble_padded[OF False qsnodouble] have pLxx: "?padded \<in> Lxx x y" .

      have E0: "T_on_rand' A s \<sigma> \<le> T_on_rand' A s ?padded"
      proof -
        have "T_on_rand' A s \<sigma> = sum (T_on_rand'_n A s \<sigma>) {..<length \<sigma>}"
          by(rule T_on_rand'_as_sum)
        also have "\<dots>
             = sum (T_on_rand'_n A s (\<sigma> @ [last \<sigma>])) {..<length \<sigma>}"
          proof(rule sum.cong, goal_cases)
            case (2 t)
            then have "t < length \<sigma>" by auto 
            then show ?case by(simp add: nth_append)
          qed simp
        also have "\<dots> \<le> T_on_rand' A s ?padded"
          unfolding ui
            apply(subst (2) T_on_rand'_as_sum) by(simp add: T_on_rand'_nn del: T_on_rand'.simps)  
        finally show ?thesis by auto
      qed  
 
      also have E1: "\<dots> \<le> c * T\<^sub>p [x,y] ?padded (OPT2 ?padded [x,y])"
        using D[OF pLxx less(2) less(5) less(3) padset] by simp
      also have E2: "\<dots> \<le> c * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 1)"
      proof -
        from False less(2) obtain \<sigma>' x' y' where qs': "\<sigma> = \<sigma>' @ [x']" and x': "x' = last \<sigma>" "y'\<noteq>x'" "y' \<in>{x,y}" 
            by (metis append_butlast_last_id insert_iff)
        have tla: "last \<sigma> \<in> {x,y}" using less(4) False last_in_set by blast
        with x' have grgr: "{x,y} = {x',y'}" by auto
        then have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')" using less(2) by auto
        then have tts: "[x, y] \<in> {[x', y'], [y', x']}" by blast
        
        from qs' ui have pd: "?padded = \<sigma>' @ [x', x']" by auto 

        have "T\<^sub>p [x,y] (?padded) (OPT2 (?padded) [x,y])
              = T\<^sub>p [x,y] (\<sigma>' @ [x', x']) (OPT2 (\<sigma>' @ [x', x']) [x,y])"
                unfolding pd by simp
        also have gr: "\<dots>
            \<le> T\<^sub>p [x,y] (\<sigma>' @ [x']) (OPT2 (\<sigma>' @ [x']) [x,y]) + 1"
              apply(rule OPT2_padded[where x="x'" and y="y'"])
                apply(fact)
                using grgr qs' less(4) by auto
        also have "\<dots> \<le> T\<^sub>p [x,y] (\<sigma>) (OPT2 (\<sigma>) [x,y]) + 1" 
              unfolding qs' by simp
        finally show ?thesis using cpos by (meson mult_left_mono of_nat_le_iff)
      qed
      also have "\<dots> =  c * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + c" by (metis (no_types, lifting) mult.commute of_nat_1 of_nat_add semiring_normalization_rules(2))
      finally show ?thesis .  
    qed
  qed 
qed
} note allg=this  

 have "T_on_rand A [x0,y0] \<sigma> \<le> c * real (T\<^sub>p [x0, y0] \<sigma> (OPT2 \<sigma> [x0, y0])) + c"  
  apply(rule allg)
    apply(fact)
    using initial apply(simp add: map_pmf_def)
    apply(fact assms(3))
    by simp
  also have "\<dots> = c * T\<^sub>p_opt [x0, y0] \<sigma> + c"
    using OPT2_is_opt[OF assms(3,1)] by(simp)
  finally show ?thesis .
qed

term "A::(nat,'is) alg_on"

theorem Phase_partitioning_general_det: 
  fixes P :: "(nat state * 'is) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
      and A :: "(nat,'is) alg_on"
  assumes xny: "(x0::nat) \<noteq> y0" 
    and cpos: "(c::real)\<ge>0"
    and static: "set \<sigma> \<subseteq> {x0,y0}" 
    and initial: "P ([x0,y0],(fst A [x0,y0])) x0 [x0,y0]"
    and D: "\<And>a b \<sigma> s.  \<sigma> \<in> Lxx a b \<Longrightarrow> a\<noteq>b \<Longrightarrow> {a,b}={x0,y0} \<Longrightarrow> P s a [x0,y0]  \<Longrightarrow> set \<sigma> \<subseteq> {a,b}
          \<Longrightarrow> T_on' A s \<sigma> \<le> c * T\<^sub>p [a,b] \<sigma> (OPT2 \<sigma> [a,b])  \<and> P (config' A s \<sigma>) (last \<sigma>) [x0,y0]"
  shows "T\<^sub>p_on A [x0,y0] \<sigma>  \<le> c * T\<^sub>p_opt [x0,y0] \<sigma> + c"
proof -
  thm Phase_partitioning_general

  thm T_deter_rand
  term T_on'
  term "embed"
  show ?thesis oops



end
