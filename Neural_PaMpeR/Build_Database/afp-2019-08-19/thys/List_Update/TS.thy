(*  Title:       Competitive Analysis of TS
    Author:      Max Haslbeck
*) 

section "TS: another 2-competitive Algorithm"

theory TS
imports
OPT2
Phase_Partitioning
Move_to_Front 
List_Factoring
RExp_Var 
begin
 

 
subsection "Definition of TS"
 

  
definition TS_step_d where
"TS_step_d s q = ((
      ( 
        let li = index (snd s) q in
        (if li = length  (snd s) then 0 \<comment> \<open>requested for first time\<close>
        else (let sincelast = take li  (snd s)
          in (let S={x. x < q in (fst s) \<and> count_list sincelast x \<le> 1}
            in
             (if S={} then 0
             else
              (index (fst s) q) - Min ( (index (fst s)) ` S)))
            )
        )      
      )
      ,[]), q#(snd s))"

 
(* FIXME: generalizing regular expressions equivalence checking 
          enables relaxing the type here to 'a::linord *)
definition rTS :: "nat list \<Rightarrow> (nat,nat list) alg_on"   where "rTS h = ((\<lambda>s. h), TS_step_d)"

fun TSstep where
  "TSstep qs n (is,s) 
      = ((qs!n)#is, 
        step s (qs!n) (( 
          let li = index is (qs!n) in
          (if li = length is then 0 \<comment> \<open>requested for first time\<close>
          else (let sincelast = take li is
            in (let S={x. x < (qs!n) in s \<and> count_list sincelast x \<le> 1}
              in
               (if S={} then 0
               else
                (index s (qs!n)) - Min ( (index s) ` S)))
              )
          )
          ),[]))"

lemma TSnopaid: "(snd (fst (snd (rTS initH) is q))) = []"
unfolding rTS_def by(simp add: TS_step_d_def)


abbreviation TSdet where
  "TSdet init initH qs n == config (rTS initH) init (take n qs)"
   
lemma TSdet_Suc: "Suc n \<le> length qs \<Longrightarrow> TSdet init initH qs (Suc n) = Step (rTS initH) (TSdet init initH qs n) (qs!n)"
by(simp add: take_Suc_conv_app_nth config_snoc)

(* now do the proof with TSdet *)

definition s_TS where "s_TS init initH qs n  = fst (TSdet init initH qs n)"

lemma sndTSdet: "n\<le>length xs \<Longrightarrow> snd (TSdet init initH xs n) = rev (take n xs) @ initH"
apply(induct n)
  apply(simp add: rTS_def)
  by(simp add: split_def TS_step_d_def take_Suc_conv_app_nth config'_snoc Step_def rTS_def)
  

subsection "Behaviour of TS on lists of length 2"

lemma 
  fixes hs x y
  assumes "x\<noteq>y"
  shows oneTS_step :    "TS_step_d ([x, y], x#y#hs)     y = ((1, []), y # x # y # hs)"
    and oneTS_stepyyy:  "TS_step_d ([x, y], y#x#hs)     y = ((Suc 0, []), y#y#x#hs)"
    and oneTS_stepx:    "TS_step_d ([x, y], x#x#hs)     y = ((0, []), y # x # x # hs)"
    and oneTS_stepy:    "TS_step_d ([x, y], [])         y = ((0, []), [y])"
    and oneTS_stepxy:   "TS_step_d ([x, y], [x])        y = ((0, []), [y, x])"
    and oneTS_stepyy:   "TS_step_d ([x, y], [y])        y = ((Suc 0, []), [y, y])"
    and oneTS_stepyx:   "TS_step_d ([x, y], hs)         x = ((0, []), x # hs)"
    using assms by(auto simp add: step_def mtf2_def swap_def TS_step_d_def before_in_def) 
   
lemmas oneTS_steps = oneTS_stepx oneTS_stepxy oneTS_stepyx oneTS_stepy oneTS_stepyy oneTS_stepyyy oneTS_step

subsection "Analysis of the Phases"

definition "TS_inv c x i \<equiv> (\<exists>hs. c = return_pmf ((if x=hd i then i else rev i),[x,x]@hs) )
                      \<or> c = return_pmf ((if x=hd i then i else rev i),[])"

lemma TS_inv_sym: "a\<noteq>b \<Longrightarrow> {a,b}={x,y} \<Longrightarrow> z\<in>{x,y} \<Longrightarrow> TS_inv c z [a,b] = TS_inv c z [x,y]"
  unfolding TS_inv_def by auto

abbreviation "TS_inv' s x i == TS_inv (return_pmf s) x i"

lemma TS_inv'_det: "TS_inv' s x i = ((\<exists>hs. s = ((if x=hd i then i else rev i),[x,x]@hs) )
                      \<or> s = ((if x=hd i then i else rev i),[]))"
  unfolding TS_inv_def by auto

lemma TS_inv'_det2: "TS_inv' (s,h) x i = (\<exists>hs. (s,h) = ((if x=hd i then i else rev i),[x,x]@hs) )
                      \<or>  (s,h) = ((if x=hd i then i else rev i),[])"
  unfolding TS_inv_def by auto

(*
TS_A   (x+1)yy \<rightarrow>         Plus(Atom (x::nat)) One,(Atom y), (Atom y)]
TS_B   (x+1)yx(yx)*yy \<rightarrow>  Plus(Atom x) One,(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom y),(Atom y)]
TS_C   (x+1)yx(yx)*x  \<rightarrow>  Plus(Atom x) One,(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom x)]
TD_D   xx             \<rightarrow>  seq[(Atom x),(Atom x)]
*)

subsubsection "(yx)*?"

lemma TS_yx': assumes "x \<noteq> y" "qs \<in> lang (Star(Times (Atom y) (Atom x)))"
      "\<exists>hs. h=[x,y]@hs"
   shows "T_on' (rTS h0) ([x,y],h) (qs@r) = length qs + T_on' (rTS h0) ([x,y],((rev qs) @h))  r
        \<and> (\<exists>hs. ((rev qs) @h) = [x, y] @ hs)
        \<and> config' (rTS h0) ([x, y],h) qs = ([x,y],rev qs @ h)"
proof -
  from assms have "qs \<in> star ({[y]} @@ {[x]})" by (simp)
  from this assms(3) show ?thesis
  proof (induct qs arbitrary: h rule: star_induct)
    case Nil
    then show ?case by(simp add: rTS_def)
  next
    case (append u v)
    then have uyx: "u = [y,x]" by auto
    from append obtain hs where a: "h = [x,y]@hs" by blast
     
    have "T_on' (rTS h0) ([x, y], (rev u @ h)) (v @ r) = length v + T_on' (rTS h0) ([x, y], rev v @ (rev u @ h)) r
        \<and> (\<exists>hs. rev v @ (rev u @ h) = [x, y] @ hs)
        \<and> config' (rTS h0) ([x, y], (rev u @ h)) v = ([x, y], rev v @ (rev u @ h))"
        apply(simp only: uyx) apply(rule append(3)) by simp
    then have yy: "T_on' (rTS h0) ([x, y], (rev u @ h)) (v @ r) = length v + T_on' (rTS h0) ([x, y], rev v @ (rev u @ h)) r"
          and history: "(\<exists>hs. rev v @ (rev u @ h) = [x, y] @ hs)"
          and state: "config' (rTS h0) ([x, y], (rev u @ h)) v = ([x, y], rev v @ (rev u @ h))" by auto
    
    have s0: "s_TS [x, y] h [y, x] 0 = [x,y]" unfolding s_TS_def by(simp) 

    from assms(1) have hahah: " {xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1} = {x}"
      unfolding before_in_def by auto
 


    have "config' (rTS h0) ([x, y],h) u = ([x, y], x # y # x # y # hs)"
        apply(simp add: split_def rTS_def uyx a ) 
          using assms(1) by(auto simp add: Step_def oneTS_steps step_def mtf2_def swap_def)
 
    then have s2: "config' (rTS h0) ([x, y],h) u =  ([x, y], ((rev u) @ h))"
        unfolding a uyx by simp

    have "config' (rTS h0) ([x, y], h) (u @ v) = 
            config' (rTS h0) (Partial_Cost_Model.config' (rTS h0) ([x, y], h) u) v" by (rule config'_append2)
  also
    have "\<dots> = config' (rTS h0)  ([x, y], ((rev u) @ h)) v" by(simp only: s2)
  also
    have "\<dots> = ([x, y], rev (u @ v) @ h)" by (simp add: state)
  finally
    have alles: "config' (rTS h0) ([x, y], h) (u @ v) = ([x, y], rev (u @ v) @ h)" .
         

    have ta: "T_on' (rTS h0) ([x,y],h) u = 2"
        unfolding rTS_def uyx a apply(simp only: T_on'.simps(2))
          using assms(1) apply(auto simp add: Step_def step_def mtf2_def swap_def oneTS_steps) 
            by(simp add: t\<^sub>p_def) 

  

    have "T_on' (rTS h0) ([x,y],h) ((u @ v) @ r)
            = T_on' (rTS h0) ([x,y],h) (u @ (v @ r))" by auto
    also have "\<dots>
        = T_on' (rTS h0) ([x,y],h) u
            + T_on' (rTS h0) (config' (rTS h0) ([x, y],h) u) (v @ r)"
        by(rule T_on'_append)
    also have "\<dots> = T_on' (rTS h0) ([x,y],h) u
          + T_on' (rTS h0) ([x, y],(rev u @ h)) (v @ r)" by(simp only: s2) 
    also have "\<dots> = T_on' (rTS h0) ([x,y],h) u + length v + T_on' (rTS h0) ([x, y], rev v @ (rev u @ h)) r" by(simp only: yy) 
    also have "\<dots> = 2 + length v + T_on' (rTS h0) ([x, y], rev v @ (rev u @ h)) r" by(simp only: ta) 
    also have "\<dots> = length (u @ v) + T_on' (rTS h0) ([x, y], rev v @ (rev u @ h)) r" using uyx by auto
    also have "\<dots> = length (u @ v) + T_on' (rTS h0) ([x, y], (rev (u @ v) @ h)) r" by auto
    finally show ?case using history alles by simp   
  qed
qed

subsubsection "?x"


lemma TS_x': "T_on' (rTS h0) ([x,y],h) [x] = 0 \<and> config' (rTS h0) ([x, y],h) [x] = ([x,y], rev [x] @ h)"
by(auto simp add: t\<^sub>p_def rTS_def TS_step_d_def Step_def step_def)
 
subsubsection "?yy"
 
lemma TS_yy': assumes "x \<noteq> y" "\<exists>hs. h = [x, y] @ hs"
  shows "T_on' (rTS h0) ([x,y],h) [y, y] = 1" "config' (rTS h0) ([x, y],h) [y,y] = ([y,x],rev [y,y] @ h)"
proof -
  from assms obtain hs where a: "h = [x,y]@hs" by blast 

  from a show "T_on' (rTS h0) ([x,y],h) [y, y] = 1"
      unfolding rTS_def 
        using assms(1) apply(auto simp add: oneTS_steps Step_def step_def mtf2_def swap_def)
           by(simp add: t\<^sub>p_def)   

  show "config' (rTS h0) ([x, y],h) [y,y] = ([y,x],rev [y,y] @ h)"
    unfolding rTS_def a using assms(1)
      by(simp add: Step_def oneTS_steps step_def mtf2_def swap_def) 
qed

subsubsection "yx(yx)*?"
 
lemma TS_yxyx': assumes [simp]: "x \<noteq> y" and "qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
  "(\<exists>hs. h=[x,x]@hs) \<or> index h y = length h"
  shows "T_on' (rTS h0) ([x,y],h) (qs@r) = length qs - 1 + T_on' (rTS h0) ([x,y],rev qs @ h) r 
        \<and> (\<exists>hs. (rev qs @ h) = [x, y] @ hs)
            \<and> config' (rTS h0) ([x, y],h) qs = ([x,y], rev qs @ h)"
proof - 
  obtain u v where uu: "u \<in> lang (Times (Atom y) (Atom x))"
                      and vv: "v \<in> lang (seq[ Star(Times (Atom y) (Atom x))])"
                      and qsuv: "qs = u @ v" 
                      using assms(2)
                      by (auto simp: conc_def)  
  from uu have uyx: "u = [y,x]" by(auto)

  from qsuv uyx have vqs: "length v = length qs - 2" by auto
  from qsuv uyx  have vqs2: "length v + 1 = length qs - 1" by auto

  have firststep: "TS_step_d ([x, y], h) y = ((0, []), y # h)"
  proof (cases "index h y = length h")
    case True
    then show ?thesis unfolding TS_step_d_def by(simp)
  next
    case False
    with assms(3) obtain hs where a: "h = [x,x]@hs" by auto
    then show ?thesis by(simp add: oneTS_steps) 
  qed

  have s2: "config' (rTS h0) ([x,y],h) u = ([x, y], x # y # h)"
    unfolding rTS_def uyx apply(simp add: )
    unfolding Step_def by(simp add: firststep step_def oneTS_steps) 
  
  have ta: "T_on' (rTS h0) ([x,y],h) u = 1"
    unfolding rTS_def uyx
      apply(simp)
      apply(simp add: firststep)
        unfolding Step_def                 
          using assms(1) by (simp add: firststep step_def oneTS_steps t\<^sub>p_def) 
 
  have ttt: 
    "T_on' (rTS h0) ([x,y],rev u @ h) (v@r) = length v + T_on' (rTS h0) ([x,y],((rev v) @(rev u @ h)))  r
      \<and> (\<exists>hs. ((rev v) @(rev u @ h)) = [x, y] @ hs)
      \<and> config' (rTS h0) ([x, y],(rev u @ h)) v = ([x,y],rev v @ (rev u @ h))"
      apply(rule TS_yx')
    apply(fact)     
    using vv apply(simp)
    using uyx by(simp) 
  then have tat: "T_on' (rTS h0) ([x,y], x # y # h) (v@r) = 
          length v + T_on' (rTS h0) ([x,y],rev qs @ h)  r" 
        and history:  "(\<exists>hs. (rev qs @ h) = [x, y] @ hs)"                                
        and state: "config' (rTS h0) ([x, y], x # y # h) v = ([x,y],rev qs @ h)" using qsuv uyx
        by auto
    
  have "config' (rTS h0) ([x, y], h) qs = config' (rTS h0) (config' (rTS h0) ([x, y], h) u) v"
    unfolding qsuv by (rule config'_append2)
also
  have "\<dots> = ([x, y], rev qs @ h)" by(simp add: s2 state) 
finally
  have his: "config' (rTS h0) ([x, y], h) qs = ([x, y], rev qs @ h)" .

 
  have "T_on' (rTS h0) ([x,y],h) (qs@r) = T_on' (rTS h0) ([x,y],h) (u @ v @ r)" using qsuv  by auto
  also have "\<dots>
      = T_on' (rTS h0) ([x,y],h) u + T_on' (rTS h0) (config' (rTS h0) ([x,y],h) u) (v @ r)"
      by(rule T_on'_append) 
  also have "\<dots> = T_on' (rTS h0) ([x,y],h) u + T_on' (rTS h0) ([x, y], x # y # h) (v @ r)" by(simp only: s2) 
  also have "\<dots> = T_on' (rTS h0) ([x,y],h) u + length v + T_on' (rTS h0) ([x,y],rev qs @ h) r" by (simp only: tat) 
  also have "\<dots> = 1 + length v + T_on' (rTS h0) ([x,y],rev qs @ h) r" by(simp only: ta) 
  also have "\<dots> = length qs - 1 + T_on' (rTS h0) ([x,y],rev qs @ h) r" using vqs2 by auto
  finally show ?thesis 
    apply(safe)
    using history apply(simp)
    using his by auto                           
qed

 
 

lemma TS_xr': assumes "x \<noteq> y" "qs \<in> lang (Plus (Atom x) One)"
   "h = [] \<or> (\<exists>hs. h = [x, x] @ hs) "
  shows "T_on' (rTS h0) ([x,y],h) (qs@r) = T_on' (rTS h0) ([x,y],rev qs@h) r"
          "((\<exists>hs. (rev qs @ h) = [x, x] @ hs) \<or> (rev qs @ h) = [x] \<or> (rev qs @ h)=[]) " 
            "config' (rTS h0) ([x,y],h) (qs@r) = config' (rTS h0) ([x,y],rev qs @ h) r"
    using assms
    by (auto simp add: T_on'_append Step_def rTS_def TS_step_d_def step_def t\<^sub>p_def) 

subsubsection "(x+1)yx(yx)*yy"

lemma ts_b': assumes "x \<noteq> y"
  "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
  "(\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []"
  shows "T_on' (rTS h0) ([x, y], h) v = (length v - 2)
            \<and>  (\<exists>hs. (rev v @ h) = [y,y]@hs) \<and> config' (rTS h0) ([x,y], h) v = ([y,x], rev v @ h)"
proof -  
  from assms have lenvmod: "length v mod 2 = 0" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star ({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[y]} @@ {[y]}" by (metis concE)
    then have "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed

  with assms(1,3) have fall: "(\<exists>hs. h = [x, x] @ hs) \<or> index h y = length h"
    by(auto)

  from assms(2) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom y, Atom y])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom y, Atom y])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[y,y]" by auto
  from aa have lena: "length a > 0" by auto
 
  from TS_yxyx'[OF assms(1) aa fall] have stars: "T_on' (rTS h0) ([x, y], h) (a @ b) =
    length a - 1 + T_on' (rTS h0) ([x, y], rev a @ h) b" 
    and history: "(\<exists>hs. rev a @ h = [x, y] @ hs)"
    and state: "config' (rTS h0) ([x, y], h) a = ([x,y],rev a @ h)" by auto 
 (* "T_on' (rTS h0) ([x,y],h) [y, y] = 1" "config' (rTS h0) ([x, y],h) [y,y] = ([y,x],rev [y,y] @ h)" *)
  have suffix: "T_on' (rTS h0) ([x, y], rev a @ h) b = 1"                                                       
     and jajajaj: "config' (rTS h0) ([x, y],rev a @ h) b = ([y,x],rev b @ rev a @ h)" unfolding bb 
    using TS_yy' history assms(1) by auto

  from stars suffix have "T_on' (rTS h0) ([x, y], h) (a @ b) = length a" using lena by auto
  then have whatineed: "T_on' (rTS h0) ([x, y], h) v = (length v - 2)" using vab bb by auto
    

  have grgr:"config' (rTS h0) ([x, y], h) v = ([y, x], rev v @ h)"
     unfolding vab 
      apply(simp only: config'_append2 state jajajaj) by simp 

  from history obtain hs' where "rev a @ h = [x, y] @ hs'" by auto
  then obtain hs2 where reva: "rev a @ h = x # hs2" by auto

  show ?thesis using whatineed grgr
    by(auto simp add: reva vab bb) 
qed
 
lemma TS_b'1: assumes "x \<noteq> y" "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
   "qs \<in> lang (seq [Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows "T_on' (rTS h0) ([x, y], h) qs = (length qs - 2)
       \<and> TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]"
proof - 
  have f: "qs \<in> lang (seq [Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
    using assms(3) by(simp add: conc_assoc)

  from ts_b'[OF assms(1) f] assms(2) have
              T_star: "T_on' (rTS h0) ([x, y], h) qs = length qs - 2"
          and inv1:   "config' (rTS h0) ([x, y],  h) qs = ([y, x], rev qs @ h)"
          and inv2:   "(\<exists>hs. rev qs @ h = [y, y] @ hs)" by auto

  from T_star have TS: "T_on' (rTS h0) ([x, y], h) qs = (length qs - 2)" by metis
  
  have lqs: "last qs = y" using assms(3) by force
 

  from inv1 have inv: "TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x, y]"
    apply(simp add: lqs)         
      apply(subst TS_inv'_det)
      using assms(2) inv2  by(simp)


  show ?thesis unfolding TS
    apply(safe) 
      by(fact inv)
qed



lemma TS_b1'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"  
   "qs \<in> lang (seq [Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T_on_rand' (embed (rTS h0)) s qs = (length qs - 2)"
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto
  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        and B: "qs \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and C: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    
    then have C': "(\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []" by blast
    from B have lqs: "last qs = y" using assms(5) by(auto simp add: conc_def)
    
    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = length qs - 2"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using ts_b'[OF A B C'] A lqs unfolding TS_inv'_det by auto
  } note b1=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule b1)
        using assms apply(simp)
        using assms apply(simp add: conc_assoc)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule b1)
          using assms apply(simp)
          using assms apply(simp add: conc_assoc)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed

         
lemma ts_b2': assumes "x \<noteq> y"
  "qs \<in> lang (seq[Atom x, Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
  "(\<exists>hs. h = [x, x] @ hs) \<or> h = []"
  shows "T_on' (rTS h0) ([x, y], h) qs = (length qs - 3)
            \<and>  config' (rTS h0) ([x,y], h) qs = ([y,x],rev qs@h) \<and> (\<exists>hs. (rev qs @ h) = [y,y]@hs)"
proof -
  from assms(2) obtain v where qs: "qs = [x]@v"
          and V: "v\<in>lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
          by(auto simp add: conc_assoc)  
 
  from assms(3) have 3: "(\<exists>hs. x#h = [x, x] @ hs) \<or> x#h = [x] \<or> x#h = []" by auto

  from ts_b'[OF assms(1) V 3]
    have T: "T_on' (rTS h0) ([x, y], x#h) v = length v - 2"
    and C: "config' (rTS h0) ([x, y], x#h) v = ([y, x], rev v @ x#h)"
    and H: "(\<exists>hs. rev v @ x#h = [y, y] @ hs)" by auto

  have t: "t\<^sub>p [x, y] x (fst (snd (rTS h0) ([x, y], h) x)) = 0"
      by (simp add: step_def rTS_def TS_step_d_def t\<^sub>p_def)
  have c: "Partial_Cost_Model.Step (rTS h0) ([x, y], h) x
            = ([x,y], x#h)" by (simp add: Step_def rTS_def TS_step_d_def step_def)

  show ?thesis
    unfolding qs apply(safe)
      apply(simp add: T_on'_append T c t)
      apply(simp add: config'_rand_append C c)
      using H by simp
qed


lemma TS_b2'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"  
   "qs \<in> lang (seq [Atom x, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T_on_rand' (embed (rTS h0)) s qs = (length qs - 3)"
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto
  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        and B: "qs \<in> lang (seq[Atom x, Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and C: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    
    from B have lqs: "last qs = y" using assms(5) by(auto simp add: conc_def)
    
    from C have C': "(\<exists>hs. h = [x, x] @ hs) \<or> h = []" by blast

    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = length qs - 3"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using ts_b2'[OF A B C'] A lqs unfolding TS_inv'_det by auto
  } note b2=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule b2)
        using assms apply(simp)
        using assms apply(simp add: conc_assoc)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule b2)
          using assms apply(simp)
          using assms apply(simp add: conc_assoc)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed



lemma TS_b': assumes "x \<noteq> y" "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
   "qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
 shows "T_on' (rTS h0) ([x, y], h) qs
    \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and> TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]"
proof -
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using assms(3)
        by (auto simp: conc_def)   
 
  from TS_xr'[OF assms(1) uu assms(2)]  have
              T_pre: "T_on' (rTS h0) ([x, y], h) (u @ v) = 
                        T_on' (rTS h0) ([x, y], rev u @ h) v"
          and fall': "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]"
          and conf: "config' (rTS h0) ([x,y],h) (u@v) = config' (rTS h0) ([x,y],rev u @ h) v"
            by auto
          
  with assms uu have fall: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> index (rev u @ h) y = length (rev u @ h)"
    by(auto) 

  from ts_b'[OF assms(1) vv fall'] have
              T_star: "T_on' (rTS h0) ([x, y], rev u @ h) v = length v - 2"
          and inv1:   "config' (rTS h0) ([x, y], rev u @ h) v = ([y, x], rev v @ rev u @ h)"
          and inv2:   "(\<exists>hs. rev v @ rev u @ h = [y, y] @ hs)" by auto

  from T_pre T_star qsuv have TS: "T_on' (rTS h0) ([x, y], h) qs = (length v - 2)" by metis

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_B) by(fact)+
 
  have lqs: "last qs = y" using assms(3) by force

  have "config' (rTS h0) ([x, y], h) qs = ([y, x], rev qs @ h)"
    unfolding qsuv conf inv1 by simp

  then have inv: "TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x, y]"
    apply(simp add: lqs)         
      apply(subst TS_inv'_det)
      using assms(2) inv2 qsuv by(simp)


  show ?thesis unfolding TS OPT
    apply(safe)
      apply(simp)
      by(fact inv)
qed


subsubsection "(x+1)yy"


lemma ts_a': assumes "x \<noteq> y" "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
   "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
  shows "TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]
          \<and> T_on' (rTS h0) ([x, y], h) qs = 2"
proof - 
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using assms(2)
        by (auto simp: conc_def)  

  from vv have vv2: "v = [y,y]" by auto 

  from uu have TS_prefix: " T_on' (rTS h0) ([x, y], h) u = 0"
   using assms(1) by(auto simp add: rTS_def oneTS_steps t\<^sub>p_def)    

  have h_split: "rev u @ h = [] \<or> rev u @ h = [x] \<or> (\<exists> hs. rev u @ h = [x,x]@hs)"
    using assms(3) uu by(auto)

  then have e: "T_on' (rTS h0) ([x,y],rev u @ h) [y,y] = 2"
      using assms(1)                    
      apply(auto simp add: rTS_def
              oneTS_steps
              Step_def step_def t\<^sub>p_def) done
        
  have conf: "config' (rTS h0) ([x, y], h) u = ([x,y], rev u @ h)"
    using uu by(auto simp add: Step_def rTS_def TS_step_d_def step_def)

  have "T_on' (rTS h0) ([x, y], h) qs = T_on' (rTS h0) ([x, y], h) (u @ v)" using qsuv  by auto
  also have "\<dots>
      =T_on' (rTS h0) ([x, y], h) u + T_on' (rTS h0) (config' (rTS h0) ([x, y], h) u) v"
      by(rule T_on'_append)
  also have "\<dots>
      = T_on' (rTS h0) ([x, y], h) u + T_on' (rTS h0) ([x,y],rev u @ h) [y,y]"
        by(simp add: conf vv2)
  also have "\<dots> = T_on' (rTS h0) ([x, y], h) u + 2" by (simp only: e)
  also have "\<dots> = 2" by (simp add: TS_prefix)
  finally have TS: "T_on' (rTS h0) ([x, y], h) qs= 2" .

  (* dannach *)
 
  have lqs: "last qs = y" using assms(2) by force

  from assms(1) have "config' (rTS h0) ([x, y], h) qs = ([y,x], rev qs @ h)"
    unfolding qsuv
    apply(simp only: config'_append2 conf vv2)
    using h_split
      apply(auto simp add: Step_def rTS_def
              oneTS_steps
              step_def)
        by(simp_all add: mtf2_def swap_def) 

  with assms(1) have "TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]"
    apply(subst TS_inv'_det)
      by(simp add: qsuv vv2 lqs)
 
  show ?thesis unfolding TS apply(auto) by fact
qed

lemma TS_a': assumes  "x \<noteq> y"
    "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
  and "qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom y])"
  shows "T_on' (rTS h0) ([x, y], h) qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
    \<and> TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x, y]
    \<and> T_on' (rTS h0) ([x, y], h) qs = 2"
proof -      
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = 1" using OPT2_A[OF assms(1,3)] by auto
  show ?thesis using OPT ts_a'[OF assms(1,3,2)] by auto  
qed 

lemma TS_a'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}" "qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y])"
 shows  
    "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T\<^sub>p_on_rand' (embed (rTS h0)) s qs = 2" 
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto

  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        "qs \<in> lang (seq [question (Atom x), Atom y, Atom y])"
        "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
     
    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = 2"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using ts_a'[OF A] by auto
  } note b=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule b)
        using assms apply(simp)
        using assms apply(simp)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule b)
          using assms apply(simp)
          using assms apply(simp)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed

subsubsection "x+yx(yx)*x"

lemma ts_c': assumes "x \<noteq> y"
  "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
  "(\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []"
  shows "T_on' (rTS h0) ([x, y], h) v = (length v - 2)
            \<and>  config' (rTS h0) ([x,y], h) v = ([x,y],rev v@h) \<and> (\<exists>hs. (rev v @ h) = [x,x]@hs)"
proof -
  from assms have lenvmod: "length v mod 2 = 1" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[x]}" by (metis concE)
    then have "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = Suc 0" by auto
  qed

  with assms(1,3) have fall: "(\<exists>hs. h = [x, x] @ hs) \<or> index h y = length h"
    by(auto) 

  

  from assms(2) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom x])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom x])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[x]" by auto
  from aa have lena: "length a > 0" by auto
 
  from TS_yxyx'[OF assms(1) aa fall] have stars: "T_on' (rTS h0) ([x, y], h) (a @ b) =
    length a - 1 + T_on' (rTS h0) ([x, y],rev a @ h) b"
    and history: "(\<exists>hs. rev a @ h = [x, y] @ hs)"
    and state: "config' (rTS h0) ([x, y], h) a =  ([x, y], rev a @ h)" by auto


  have suffix: "T_on' (rTS h0) ( [x, y],rev a @ h) b = 0"
          and suState: "config' (rTS h0) ([x, y], rev a @ h) b = ([x,y], rev b @ (rev a @ h))"
    unfolding bb using TS_x' by auto 

  from stars suffix have "T_on' (rTS h0) ([x, y], h) (a @ b) = length a - 1" by auto
  then have whatineed: "T_on' (rTS h0) ([x, y], h) v = (length v - 2)" using vab bb by auto

  have conf: "config' (rTS h0) ([x, y], h) v = ([x, y], rev v @ h)" 
    by(simp add: vab config'_append2 state suState) 

 
  from history obtain hs' where "rev a @ h = [x, y] @ hs'" by auto
  then obtain hs2 where reva: "rev a @ h = x # hs2" by auto


  show ?thesis using whatineed
    apply(auto) 
      using conf apply(simp)
      by(simp add: reva vab bb)
qed


lemma TS_c1'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"  
   "qs \<in> lang (seq [Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x])"
 shows "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T_on_rand' (embed (rTS h0)) s qs = (length qs - 2)"
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto
  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        and B: "qs \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and C: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    
    then have C': "(\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []" by blast
    from B have lqs: "last qs = x" using assms(5) by(auto simp add: conc_def)
    
    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = length qs - 2"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using ts_c'[OF A B C'] A lqs unfolding TS_inv'_det by auto
  } note c1=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule c1)
        using assms apply(simp)
        using assms apply(simp add: conc_assoc)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule c1)
          using assms apply(simp)
          using assms apply(simp add: conc_assoc)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed
         
lemma ts_c2': assumes "x \<noteq> y"
  "qs \<in> lang (seq[Atom x, Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
  "(\<exists>hs. h = [x, x] @ hs) \<or> h = []"
  shows "T_on' (rTS h0) ([x, y], h) qs = (length qs - 3)
            \<and>  config' (rTS h0) ([x,y], h) qs = ([x,y],rev qs@h) \<and> (\<exists>hs. (rev qs @ h) = [x,x]@hs)"
proof -
  from assms(2) obtain v where qs: "qs = [x]@v"
          and V: "v\<in>lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
          by(auto simp add: conc_assoc)  
 
  from assms(3) have 3: "(\<exists>hs. x#h = [x, x] @ hs) \<or> x#h = [x] \<or> x#h = []" by auto

  from ts_c'[OF assms(1) V 3]
    have T: "T_on' (rTS h0) ([x, y], x#h) v = length v - 2"
    and C: "config' (rTS h0) ([x, y], x#h) v = ([x, y], rev v @ x#h)"
    and H: "(\<exists>hs. rev v @ x#h = [x, x] @ hs)" by auto

  have t: "t\<^sub>p [x, y] x (fst (snd (rTS h0) ([x, y], h) x)) = 0"
      by (simp add: step_def rTS_def TS_step_d_def t\<^sub>p_def)
  have c: "Partial_Cost_Model.Step (rTS h0) ([x, y], h) x
            = ([x,y], x#h)" by (simp add: Step_def rTS_def TS_step_d_def step_def)

  show ?thesis
    unfolding qs apply(safe)
      apply(simp add: T_on'_append T c t)
      apply(simp add: config'_rand_append C c)
      using H by simp
qed


lemma TS_c2'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"  
   "qs \<in> lang (seq [Atom x, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x])"
 shows "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T_on_rand' (embed (rTS h0)) s qs = (length qs - 3)"
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto
  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        and B: "qs \<in> lang (seq[Atom x, Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and C: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    
    from B have lqs: "last qs = x" using assms(5) by(auto simp add: conc_def)
    
    from C have C': "(\<exists>hs. h = [x, x] @ hs) \<or> h = []" by blast

    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = length qs - 3"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using ts_c2'[OF A B C'] A lqs unfolding TS_inv'_det by auto
  } note c2=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule c2)
        using assms apply(simp)
        using assms apply(simp add: conc_assoc)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule c2)
          using assms apply(simp)
          using assms apply(simp add: conc_assoc)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed


lemma TS_c': assumes "x \<noteq> y" "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
  "qs \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom x])"
  shows "T_on' (rTS h0) ([x, y], h) qs
    \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and>  TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]"
proof -
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and qsuv: "qs = u @ v" 
        using assms(3)
        by (auto simp: conc_def)   
 
  from TS_xr'[OF assms(1) uu assms(2)] have
              T_pre: "T_on' (rTS h0) ([x, y], h) (u@v) = T_on' (rTS h0) ([x, y], rev u @ h) v"
          and fall': "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]"
          and conf': "config' (rTS h0) ([x, y], h) (u @ v) =
                config' (rTS h0) ([x, y], rev u @ h) v" by auto
      
  with assms uu have fall: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> index (rev u @ h) y = length (rev u @ h)"
    by(auto) 

  from ts_c'[OF assms(1) vv fall'] have
              T_star: "T_on' (rTS h0) ([x, y], rev u @ h) v = (length v - 2)"
          and inv1:   "config' (rTS h0) ([x, y], (rev u @ h)) v = ([x, y], rev v @ rev u @ h)"
          and inv2:   "(\<exists>hs. rev v @ rev u @ h = [x, x] @ hs)" by auto

  from T_pre T_star qsuv have TS: "T_on' (rTS h0) ([x, y], h) qs = (length v - 2)" by metis

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_C) by(fact)+
     
  have lqs: "last qs = x" using assms(3) by force

  have conf: "config' (rTS h0) ([x, y], h) qs = ([x, y], rev qs @ h)"
    by(simp add: qsuv conf' inv1)
  then have conf: "TS_inv' (config' (rTS h0) ([x, y], h) qs) (last qs) [x,y]"
    apply(simp add: lqs)
      apply( subst TS_inv'_det)
       using inv2 qsuv by(simp)
 
  show ?thesis unfolding TS OPT
    by (auto simp add: conf) 
qed



subsubsection "xx"

lemma request_first: "x\<noteq>y \<Longrightarrow> Step (rTS h) ([x, y], is) x = ([x,y],x#is)"
unfolding rTS_def Step_def by(simp add: split_def TS_step_d_def step_def)

lemma ts_d': "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow>
    T_on' (rTS h0) ([x, y], h) qs = 0 \<and>
     TS_inv' (config' (rTS h0) ([x, y], h) qs) x [x,y]"
proof -
  assume xny: "x \<noteq> y"
  assume "qs \<in> lang (seq [Atom x, Atom x])"
  then have xx: "qs = [x,x]" by auto

  from xny have TS: "T_on' (rTS h0) ([x, y], h) qs = 0" unfolding xx
      by(auto simp add: Step_def step_def oneTS_steps rTS_def  t\<^sub>p_def) 

  from xny have "config' (rTS h0) ([x, y], h) qs = ([x, y], x # x # h) "
    by(auto simp add: xx Step_def rTS_def oneTS_steps step_def)
      
  then have " TS_inv' (config' (rTS h0) ([x, y], h) qs) x [x, y]"
    by(simp add: TS_inv'_det)
      
  with TS  show ?thesis by simp  
qed



lemma TS_d': assumes xny: "x \<noteq> y" and "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    and qsis: "qs \<in> lang (seq [Atom x, Atom x])"
    shows "T_on' (rTS h0) ([x,y],h) qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) "
      and "TS_inv' (config' (rTS h0) ([x,y],h) qs)  (last qs) [x, y]"
      and "T_on' (rTS h0) ([x,y],h) qs = 0"
proof -
  from qsis have xx: "qs = [x,x]" by auto

  show TS: "T_on' (rTS h0) ([x,y],h) qs = 0"  
    using assms(1) by (auto simp add: xx t\<^sub>p_def rTS_def Step_def oneTS_steps step_def) 
  then show "T_on' (rTS h0) ([x,y],h) qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" by simp

  show "TS_inv' (config' (rTS h0) ([x,y],h) qs)  (last qs) [x, y]"
    unfolding TS_inv_def
      by(simp add: xx request_first[OF xny]) 
qed


lemma TS_d'': assumes 
    "x \<noteq> y" "{x, y} = {x0, y0}" "TS_inv s x [x0, y0]"
    "set qs \<subseteq> {x, y}"  
   "qs \<in> lang (seq [Atom x, Atom x])"
 shows "TS_inv (config'_rand (embed (rTS h0)) s qs) (last qs) [x0, y0]
      \<and> T_on_rand' (embed (rTS h0)) s qs = 0"
proof -
  from assms(1,2) have kas: "(x0=x \<and> y0=y) \<or> (y0=x \<and> x0=y)" by(auto)
  then obtain h where S: "s = return_pmf ([x,y],h)" and h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    apply(rule disjE) using assms(1,3) unfolding TS_inv_def by(auto) 
  
  have l: "qs \<noteq> []" using assms by auto
  {
    fix x y qs h0
    fix h:: "nat list"
    assume A: "x \<noteq> y"
        and B: "qs \<in> lang (seq [Atom x, Atom x])"
        and C: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
    
    from B have lqs: "last qs = x" using assms(5) by(auto simp add: conc_def)
     

    have "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) qs) (last qs) [x, y] \<and>
            T_on_rand' (embed (rTS h0)) (return_pmf ([x, y], h)) qs = 0"
      apply(simp only: T_on'_embed[symmetric] config'_embed)
      using TS_d'[OF A C B ] A lqs unfolding TS_inv'_det by auto
  } note d=this
   

  show ?thesis unfolding S 
    using kas apply(rule disjE)
      apply(simp only:)
      apply(rule d)
        using assms apply(simp)
        using assms apply(simp add: conc_assoc)
        using h apply(simp)
      apply(simp only:)
      
      apply(subst TS_inv_sym[of y x x y])
        using assms(1) apply(simp)
        apply(blast)
        defer
        apply(rule d)
          using assms apply(simp)
          using assms apply(simp add: conc_assoc)
          using h apply(simp)
        using last_in_set l assms(4) by blast
qed



subsection "Phase Partitioning"
 
lemma D': assumes "\<sigma>' \<in> Lxx x y" and "x \<noteq> y" and "TS_inv' ([x, y], h) x [x, y]"
  shows  "T_on' (rTS h0) ([x, y], h) \<sigma>' \<le> 2 * T\<^sub>p [x, y] \<sigma>' (OPT2 \<sigma>' [x, y]) 
      \<and>  TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) \<sigma>') (last \<sigma>') [x, y]"
proof -

  from config'_embed have " config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) \<sigma>' 
      = return_pmf (Partial_Cost_Model.config' (rTS h0) ([x, y], h) \<sigma>')" by blast

  then have L: "TS_inv (config'_rand (embed (rTS h0)) (return_pmf ([x, y], h)) \<sigma>') (last \<sigma>') [x, y]
      = TS_inv' (config' (rTS h0) ([x, y], h) \<sigma>')  (last \<sigma>') [x, y]" by auto
 
  from assms(3) have 
      h: "h = [] \<or> (\<exists>hs. h = [x, x] @ hs)"
      by(auto simp add: TS_inv'_det) 

  have "T_on' (rTS h0) ([x, y], h) \<sigma>' \<le> 2 * T\<^sub>p [x, y] \<sigma>' (OPT2 \<sigma>' [x, y]) 
      \<and>  TS_inv' (config' (rTS h0) ([x, y], h) \<sigma>')  (last \<sigma>') [x, y]"  
  apply(rule LxxE[OF assms(1)])
    using TS_d'[OF assms(2) h, of "\<sigma>'"] apply(simp)
    using TS_b'[OF assms(2) h] apply(simp)
    using TS_c'[OF assms(2) h] apply(simp)
    using TS_a'[OF assms(2) h] apply fast
    done 

  then show ?thesis using L by auto
qed

theorem TS_OPT2':  "(x::nat) \<noteq> y \<Longrightarrow> set \<sigma> \<subseteq> {x,y}
     \<Longrightarrow> T\<^sub>p_on (rTS []) [x,y] \<sigma>  \<le> 2 * real (T\<^sub>p_opt [x,y] \<sigma>) + 2"
apply(subst T_on_embed)   
  apply(rule Phase_partitioning_general[where P=TS_inv])
      apply(simp)
     apply(simp)
    apply(simp)
   apply(simp add: TS_inv_def rTS_def) 
  proof (goal_cases)
    case (1 a b \<sigma>' s)
    from 1(6) obtain h hist' where s: "s = return_pmf ([a, b], h)" 
            and "h = [] \<or> h = [a,a]@hist'"
      unfolding TS_inv_def apply(cases "a=hd [x,y]")
        apply(simp) using 1 apply fast
        apply(simp) using 1 by blast
         
    from 1 have xyab: "TS_inv' ([a, b], h) a [x, y]
          = TS_inv' ([a, b], h) a [a, b]"
           by(auto simp add: TS_inv'_det)

    with 1(6) s have inv: "TS_inv' ([a, b], h) a [a, b]" by simp

    from \<open>\<sigma>' \<in> Lxx a b\<close> have "\<sigma>' \<noteq> []" using Lxx1 by fastforce
    then have l: "last \<sigma>' \<in> {x,y}" using 1(5,7) last_in_set by blast

    show ?case unfolding s T_on'_embed[symmetric]
      using D'[OF 1(3,4) inv, of "[]"]
        apply(safe)
         apply linarith
        using TS_inv_sym[OF 1(4,5)] l apply blast 
       done
  qed
  
subsection "TS is pairwise"

 

lemma config'_distinct[simp]: 
  shows "distinct (fst (config' A S qs)) = distinct (fst S)" 
apply (induct qs rule: rev_induct) by(simp_all add: config'_snoc Step_def split_def distinct_step)

lemma config'_set[simp]: 
  shows "set (fst (config' A S qs)) = set (fst S)" 
apply (induct qs rule: rev_induct) by(simp_all add: config'_snoc Step_def split_def set_step)
 
lemma s_TS_append: "i\<le>length as \<Longrightarrow>s_TS init h (as@bs) i = s_TS init h as i"
by (simp add: s_TS_def)

lemma s_TS_distinct: "distinct init \<Longrightarrow> i<length qs \<Longrightarrow> distinct (fst (TSdet init h qs i))"
by(simp_all add: config_config_distinct)

lemma othersdontinterfere: "distinct init \<Longrightarrow> i < length qs \<Longrightarrow> a\<in>set init \<Longrightarrow> b\<in>set init
     \<Longrightarrow> set qs \<subseteq> set init \<Longrightarrow> qs!i\<notin>{a,b} \<Longrightarrow> a < b in s_TS init h qs i \<Longrightarrow> a < b in s_TS init h qs (Suc i)"
apply(simp add: s_TS_def split_def take_Suc_conv_app_nth config_append Step_def step_def)
  apply(subst x_stays_before_y_if_y_not_moved_to_front)
    apply(simp_all add: config_config_distinct config_config_set)
    by(auto simp: rTS_def TS_step_d_def) 

lemma  TS_mono:
    fixes l::nat
    assumes 1: "x < y in s_TS init h xs (length xs)"
     and l_in_cs: "l \<le> length cs"
     and firstocc: "\<forall>j<l. cs ! j \<noteq> y"
     and "x \<notin> set cs" 
     and di: "distinct init"  
     and inin: "set (xs @ cs) \<subseteq> set init"
    shows "x < y in s_TS init h (xs@cs) (length (xs)+l)"
proof -                                               
  from before_in_setD2[OF 1] have y: "y : set init" unfolding s_TS_def by(simp add: config_config_set)
  from before_in_setD1[OF 1] have x: "x : set init" unfolding s_TS_def by(simp add: config_config_set)

  {
      fix n
      assume "n\<le>l"
      then have "x < y in s_TS init h ((xs)@cs) (length (xs)+n)"
        proof(induct n)
          case 0
          show ?case apply (simp only: s_TS_append ) using 1 by(simp) 
        next
          case (Suc n) 
          then have n_lt_l: "n<l" by auto
          show ?case apply(simp)
            apply(rule othersdontinterfere)
              apply(rule di)
              using n_lt_l l_in_cs apply(simp)
              apply(fact x)
              apply(fact y)
              apply(fact inin)
              apply(simp add: nth_append) apply(safe)
                using assms(4) n_lt_l l_in_cs apply fastforce
                using firstocc n_lt_l apply blast
                using Suc(1) n_lt_l by(simp)
        qed  
    }
    \<comment> \<open>before the request to y, x is in front of y\<close>
    then show "x < y in s_TS init h (xs@cs) (length (xs)+l)"
      by blast
qed

lemma step_no_action: "step s q (0,[]) = s"
unfolding step_def mtf2_def by simp

lemma s_TS_set: "i \<le> length qs \<Longrightarrow> set (s_TS init h qs i) = set init"
apply(induct i)
  apply(simp add: s_TS_def  )
  apply(simp add: s_TS_def TSdet_Suc)
  by(simp add: split_def rTS_def Step_def step_def)

lemma count_notin2: "count_list xs x = 0 \<Longrightarrow> x \<notin> set xs"
apply (induction xs)  apply (auto del: count_notin)
  apply(case_tac "a=x") by(simp_all)+

lemma count_append: "count_list (xs@ys) x = count_list xs x + count_list ys x"
apply(induct xs) by(simp_all)

lemma count_rev: "count_list (rev xs) x = count_list xs x"
apply(induct xs) by(simp_all add: count_append )
 
lemma mtf2_q_passes: assumes "q \<in> set xs" "distinct xs" 
  and "index xs q - n \<le> index xs x" "index xs x < index xs q"
  shows "q < x in (mtf2 n q xs)"
proof -
  from assms have "index xs q < length xs" by auto
  with assms(4) have ind_x: "index xs x < length xs" by auto
  then have xinxs: "x\<in>set xs" using index_less_size_conv by metis 

  have B: "index (mtf2 n q xs) q = index xs q - n"
    apply(rule mtf2_q_after)
      by(fact)+
  also from ind_x mtf2_forward_effect3'[OF assms]
      have A: "\<dots> < index (mtf2 n q xs) x" by auto 
  finally show ?thesis unfolding before_in_def using xinxs by force
qed
                
lemma twotox:
    assumes "count_list bs y \<le> 1"
      and "distinct init"
      and "x \<in> set init"
      and "y : set init" 
      and "x \<notin> set bs"
      and "x\<noteq>y"
    shows "x < y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))"
proof -
  have aa: "snd (TSdet init h ((as @ x # bs) @ [x]) (Suc (length as + length bs)))
        = rev (take (Suc (length as + length bs)) ((as @ x # bs) @ [x])) @ h"
          apply(rule sndTSdet)  by(simp)
  then have aa': "snd (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))
        = rev (take (Suc (length as + length bs)) ((as @ x # bs) @ [x])) @ h" by auto
  have lasocc_x: "index (snd (TSdet init h ((as @ x # bs) @ [x]) (Suc (length as + length bs)))) x = length bs"
    unfolding aa
    apply(simp add:  del: config'.simps)
    using assms(5) by(simp add: index_append) 
  then have lasocc_x': "(index (snd (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x) = length bs" by auto

  let ?sincelast = "take (length bs)
                          (snd (TSdet init h ((as @ x # bs) @ [x])
                                 (Suc (length as + length bs))))"
  have sl: "?sincelast  = rev bs" unfolding aa by(simp)
  let ?S = "{xa. xa < x in fst (TSdet init h (as @ x # bs @ [x])
                                      (Suc (length as + length bs))) \<and>
                             count_list ?sincelast xa \<le> 1}"

  have y: "y \<in> ?S \<or> ~  y < x  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))"
    unfolding sl unfolding s_TS_def using assms(1) by(simp add: count_rev del: config'.simps)
 
    have eklr: "length (as@[x]@bs@[x]) = Suc (length (as@[x]@bs))" by simp
  have 1: "s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))
     = fst (Partial_Cost_Model.Step (rTS h)
          (TSdet init h (as @ [x] @ bs @ [x])
            (length (as @ [x] @ bs)))
          ((as @ [x] @ bs @ [x]) ! length (as @ [x] @ bs)))" unfolding s_TS_def unfolding eklr apply(subst TSdet_Suc)
              by(simp_all add: split_def)

  have brrr: "x\<in> set (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))"
    apply(subst s_TS_set[unfolded s_TS_def])
      apply(simp) by fact
  have ydrin: "y\<in>set (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))" 
    apply(subst s_TS_set[unfolded s_TS_def]) apply(simp) by fact
  have dbrrr: "distinct (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))" 
    apply(subst s_TS_distinct[unfolded s_TS_def]) using assms(2) by(simp_all)

  show ?thesis
  proof (cases "y < x  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))")
    case True
    with y have yS: "y\<in>?S" by auto
    then have minsteps: "Min (index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) ` ?S)
              \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y"
      by auto
    let ?entf = "index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x -
                           Min (index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) ` ?S)"
    from minsteps have br: " index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x - (?entf)
          \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y" 
          by presburger
    have brr: "index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        < index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x"
          using True unfolding before_in_def s_TS_def by auto

    from br brr have klo: " index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x - (?entf)
          \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        \<and> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        < index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x" by metis
   
 
    let ?result ="(mtf2 ?entf x (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))))"

    have whatsthat: "s_TS init h (as @ [x] @ bs @ [x]) (length (as @ [x] @ bs @ [x]))
        = ?result"   
        unfolding 1 apply(simp add: split_def step_def rTS_def Step_def TS_step_d_def del: config'.simps)
        apply(simp add: nth_append del: config'.simps)
          using lasocc_x'[unfolded rTS_def] aa'[unfolded rTS_def]
            apply(simp add:  del: config'.simps)
          using yS[unfolded sl rTS_def] by auto  


    have ydrinee: "  y \<in> set (mtf2 ?entf x (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))))" 
      apply(subst set_mtf2)  
      apply(subst s_TS_set[unfolded s_TS_def]) apply(simp) by fact

    show ?thesis unfolding whatsthat apply(rule mtf2_q_passes) by(fact)+       
  next
    case False
    then have 2: "x < y  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))" 
      using brrr ydrin not_before_in assms(6) unfolding s_TS_def by metis 
    {
      fix e
      have "x < y in mtf2 e x (s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs)))"
        apply(rule x_stays_before_y_if_y_not_moved_to_front)
          unfolding s_TS_def
          apply(fact)+
          using assms(6) apply(simp)
          using 2 unfolding s_TS_def by simp
    } note bratz=this
    show ?thesis unfolding 1 apply(simp add: TSnopaid split_def Step_def s_TS_def TS_step_d_def step_def nth_append  del: config'.simps)
            using bratz[unfolded s_TS_def] by simp  
  qed

qed

lemma count_drop: "count_list (drop n cs) x \<le> count_list cs x"
proof -
  have "count_list cs x = count_list (take n cs @ drop n cs) x" by auto
  also have "\<dots> = count_list (take n cs) x + count_list (drop n cs) x" by (rule count_append)
  also have "\<dots> \<ge> count_list (drop n cs) x" by auto
  finally show ?thesis .
qed

lemma count_take_less: assumes "n\<le>m" 
  shows "count_list (take n cs) x \<le> count_list (take m cs) x"
proof -
    from assms have "count_list (take n cs) x = count_list (take n (take m cs)) x" by auto
    also have "\<dots> \<le> count_list (take n (take m cs) @ drop n (take m cs)) x" by (simp only: count_append)
    also have "\<dots> = count_list (take m cs) x" 
        by(simp only: append_take_drop_id)
    finally show ?thesis .
qed

lemma count_take: "count_list (take n cs) x \<le> count_list cs x"
proof -
  have "count_list cs x = count_list (take n cs @ drop n cs) x" by auto
  also have "\<dots> = count_list (take n cs) x + count_list (drop n cs) x" by (rule count_append)
  also have "\<dots> \<ge> count_list (take n cs) x" by auto
  finally show ?thesis .
qed

lemma casexxy: assumes "\<sigma>=as@[x]@bs@[x]@cs"
    and "x \<notin> set cs"
    and "set cs \<subseteq> set init"
    and "x \<in> set init"
    and "distinct init"
    and "x \<notin> set bs"
    and "set as \<subseteq> set init"
    and "set bs \<subseteq> set init"
  shows "(%i. i<length cs \<longrightarrow> (\<forall>j<i. cs!j\<noteq>cs!i) \<longrightarrow> cs!i\<noteq>x
      \<longrightarrow> (cs!i) \<notin> set bs
      \<longrightarrow> x < (cs!i) in  (s_TS init h \<sigma> (length (as@[x]@bs@[x]) + i+1))) i"
proof (rule infinite_descent[where P="(%i. i<length cs \<longrightarrow> (\<forall>j<i. cs!j\<noteq>cs!i) \<longrightarrow> cs!i\<noteq>x
      \<longrightarrow> (cs!i) \<notin> set bs
      \<longrightarrow> x < (cs!i) in  (s_TS init h \<sigma> (length (as@[x]@bs@[x]) + i+1)))"], goal_cases)
  case (1 i) 
  let ?y = "cs!i" 
  from 1 have i_in_cs: "i < length cs" and
      firstocc: "(\<forall>j<i. cs ! j \<noteq> cs ! i)"
      and ynx: "cs ! i \<noteq> x"
      and ynotinbs: "cs ! i \<notin> set bs"
      and y_before_x': "~x < cs ! i in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)" by auto

  have ss: "set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)) = set init" using assms(1) i_in_cs by(simp add: s_TS_set)
  then have "cs ! i \<in> set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1))"
    unfolding ss using assms(3) i_in_cs by fastforce
  moreover have "x : set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1))"
    unfolding ss using assms(4) by fastforce

  \<comment> \<open>after the request to y, y is in front of x\<close>
  ultimately have y_before_x_Suct3: "?y < x in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)"
      using  y_before_x' ynx not_before_in by metis

  from ynotinbs have yatmostonceinbs: "count_list bs (cs!i) \<le> 1" by simp
 

  let ?y = "cs!i"
  have yininit: "?y \<in> set init" using assms(3) i_in_cs by fastforce
  {
    fix y
    assume "y \<in> set init"
    assume "x\<noteq>y"
    assume "count_list bs y \<le> 1"
    then have "x < y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))"
      apply(rule twotox) by(fact)+
  } note xgoestofront=this    
  with yatmostonceinbs ynx yininit have zeitpunktt2: "x < ?y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))" by blast
 
  have "i \<le> length cs" using i_in_cs by auto
  have x_before_y_t3: "x < ?y in s_TS init h ((as@[x]@bs@[x])@cs) (length (as@[x]@bs@[x])+i)"
    apply(rule TS_mono)
      apply(fact)+
      using assms by simp
  \<comment> \<open>so x and y swap positions when y is requested, that means that y was inserted infront of
      some elment z (which cannot be x, has only been requested at most once since last request of y
          but is in front of x)\<close>

  \<comment> \<open>first show that y must have been requested in as\<close>
  
  have "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i)) =
          rev (take (length (as @ [x] @ bs @ [x]) + i) (as @ [x] @ bs @ [x] @ cs)) @ h"
            apply(rule sndTSdet) using i_in_cs by simp
  also have "\<dots>  = (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" by simp
  finally have fstTS_t3: "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i)) = 
                (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" .
  then have fstTS_t3': "(snd (TSdet init h \<sigma> (Suc (Suc (length as + length bs + i))))) = 
                (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" using assms(1) by auto

  let ?is = "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i))"
  let ?is' = "snd (config (rTS h) init (as @ [x] @ bs @ [x] @ (take i cs)))"
  let ?s = "fst (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i))"
  let ?s' = "fst (config (rTS h) init (as @ [x] @ bs @ [x] @ (take i cs)))"
  let ?s_Suct3="s_TS init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i+1)" 

  let ?S = "{xa. (xa < (as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i) in ?s \<and>
            count_list (take (index ?is ((as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i))) ?is) xa \<le> 1) }"
  let ?S' = "{xa. (xa < (as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i) in ?s' \<and>
            count_list (take (index ?is' ((cs!i))) ?is') xa \<le> 1) }"

  have isis': "?is = ?is'" by(simp)
  have ss': "?s = ?s'" by(simp)
  then have SS': "?S = ?S'" using i_in_cs by(simp add: nth_append)


  (* unfold TSdet once *) 
  have once: "TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (Suc (length as + length bs + i))))
        = Step (rTS h) (config\<^sub>p (rTS h) init (as @ x # bs @ x # take i cs)) (cs ! i)"
    apply(subst TSdet_Suc)
      using i_in_cs apply(simp)
      by(simp add: nth_append) 

  have aha: "(index ?is (cs ! i) \<noteq> length ?is) 
        \<and> ?S \<noteq> {}"
  proof (rule ccontr, goal_cases)
    case 1
    then have "(index ?is (cs ! i) = length ?is) \<or> ?S = {}" by(simp)
    then have alters: "(index ?is' (cs ! i) = length ?is') \<or> ?S' = {}"
      apply(simp only: SS') by(simp only: isis')
    \<comment> \<open>wenn (cs ! i) noch nie requested wurde, dann kann es gar nicht nach vorne gebracht werden!
        also widerspruch mit @{text y_before_x'}\<close> 
    have "?s_Suct3 = fst (config (rTS h) init ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)))"
      unfolding s_TS_def
      apply(simp only: length_append)
        apply(subst take_append)
        apply(subst take_append)
        apply(subst take_append)
        apply(subst take_append) 
        by(simp)
    also have "\<dots> =  fst (config (rTS h) init (((as @ [x] @ bs @ [x]) @ (take i cs)) @ [cs!i]))"
      using i_in_cs by(simp add: take_Suc_conv_app_nth)
    also have "\<dots> = step ?s' ?y (0, [])"
      proof (cases "index ?is' (cs ! i) = length ?is'")
        case True
        show ?thesis 
          apply(subst config_append)
          using i_in_cs apply(simp add: rTS_def Step_def split_def nth_append)
          apply(subst TS_step_d_def)
          apply(simp only: True[unfolded rTS_def,simplified])
          by(simp)
      next
        case False 
        with alters have S': "?S' = {}" by simp

        have 1 : "{xa. xa < cs ! i
                                 in fst (Partial_Cost_Model.config' (\<lambda>s. h, TS_step_d) (init, h)
                                          (as @ x # bs @ x # take i cs)) \<and>
                                 count_list (take (index
                (snd
                  (Partial_Cost_Model.config'
                    (\<lambda>s. h, TS_step_d) (init, h)
                    (as @ x # bs @ x # take i cs)))
                (cs ! i))
                        (snd
                          (Partial_Cost_Model.config'
(\<lambda>s. h, TS_step_d) (init, h)
(as @ x # bs @ x # take i cs)))) xa \<le> 1} = {}" using S' by(simp add: rTS_def nth_append)

        show ?thesis 
          apply(subst config_append)
          using i_in_cs apply(simp add: rTS_def Step_def split_def nth_append)
          apply(subst TS_step_d_def)  
          apply(simp only: 1 Let_def)
          by(simp)
      qed
    finally have "?s_Suct3 = step ?s ?y (0, [])" using ss' by simp
    then have e: "?s_Suct3 = ?s" by(simp only: step_no_action)
    from x_before_y_t3 have "x < cs ! i in ?s_Suct3" unfolding e unfolding s_TS_def by simp     
    with y_before_x' show "False" unfolding assms(1) by auto
  qed  
  then have aha': "index (snd (TSdet init h (as @ x # bs @ x # cs)  (Suc (Suc (length as + length bs + i)))))
 (cs ! i) \<noteq>
length (snd (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (length as + length bs + i)))))" 
      and
      aha2: "?S \<noteq> {}" by auto
      

  from fstTS_t3' assms(1) have is_: "?is = (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" by auto
    
   have minlencsi: " min (length cs) i = i" using i_in_cs by linarith 

   let ?lastoccy="(index (rev (take i cs) @ x # rev bs @ x # rev as @ h) (cs ! i))"
   have "?y \<notin> set (rev (take i cs))" using firstocc by (simp add: in_set_conv_nth)
   then have lastoccy: "?lastoccy \<ge>
            i + 1 + length bs + 1" using ynx ynotinbs minlencsi by(simp add: index_append)

  (* x is not in S, because it is requested at least twice since the last request to y*)
  have x_nin_S: "x\<notin>?S"
      using is_ apply(simp add: split_def nth_append del: config'.simps)
  proof (goal_cases)
    case 1
     have " count_list (take ?lastoccy (rev (take i cs))) x \<le>
          count_list (drop (length cs - i) (rev cs)) x" by (simp add: count_take rev_take)
     also have "\<dots> \<le> count_list (rev cs) x" by(simp add: count_drop ) 
     also have "\<dots> = 0" using assms(2) by(simp add: count_rev)
     finally have " count_list (take ?lastoccy (rev (take i cs))) x = 0" by auto
     have"
        2 \<le>
        count_list ([x] @ rev bs @ [x]) x " apply(simp only: count_append) by(simp)
     also have "\<dots> = count_list (take (1 + length bs + 1) (x # rev bs @ x # rev as @ h)) x" by auto
     also have "\<dots> \<le> count_list (take (?lastoccy - i) (x # rev bs @ x # rev as @ h)) x"
                apply(rule count_take_less)
                    using lastoccy by linarith
     also have   "\<dots> \<le>  count_list (take ?lastoccy (rev (take i cs))) x
                      + count_list (take (?lastoccy - i) (x # rev bs @ x # rev as @ h)) x" by auto
     also have "\<dots> = count_list (take ?lastoccy (rev (take i cs))
                            @ take (?lastoccy - min (length cs) i)
                            (x # rev bs @ x # rev as @ h)) x"
               by(simp add: minlencsi count_append) 
     finally show ?case by presburger
  qed

  have "Min (index ?s ` ?S) \<in> (index ?s ` ?S)" apply(rule Min_in) using aha2 by (simp_all)
  then obtain z where zminimal: "index ?s z = Min (index ?s ` ?S)"and z_in_S: "z \<in> ?S" by auto
  then have bef: "z < (as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i) in ?s"
          and "count_list (take (index ?is ((as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i))) ?is) z \<le> 1" by(blast)+ 

  with zminimal have zbeforey: "z < cs ! i in ?s"
    and zatmostonce: "count_list (take (index ?is (cs ! i)) ?is) z \<le> 1"
    and isminimal: "index ?s z = Min (index ?s ` ?S)" by(simp_all add: nth_append) 
  have elemins: "z \<in> set ?s" unfolding before_in_def by (meson zbeforey before_in_setD1)
  then  have zininit: "z \<in> set init"
    using i_in_cs by(simp add: s_TS_set[unfolded s_TS_def] del: config'.simps) 

  from zbeforey have zbeforey_ind: "index ?s z < index ?s ?y" unfolding before_in_def by auto
  then have el_n_y: "z \<noteq> ?y" by auto

  have el_n_x: "z \<noteq> x" using x_nin_S  z_in_S by blast

  (* and because it is JUST before that element, z must be before x *)
  { fix s q
    have TS_step_d2: "TS_step_d s q =
      (let V\<^sub>r={x. x < q in fst s \<and> count_list (take (index (snd s) q) (snd s)) x \<le> 1}
       in ((if index (snd s) q \<noteq> length (snd s) \<and> V\<^sub>r \<noteq> {}
          then index (fst s) q - Min ( (index (fst s)) ` V\<^sub>r)
          else 0,[]),q#(snd s)))"
    unfolding TS_step_d_def 
    apply(cases "index (snd s) q < length (snd s)") 
     using index_le_size apply(simp split: prod.split) apply blast
    by(auto simp add: index_less_size_conv split: prod.split)
  } note alt_chara=this

  have iF: "(index (snd (config' (\<lambda>s. h, TS_step_d) (init, h) (as @ x # bs @ x # take i cs))) (cs ! i)
               \<noteq> length (snd (config' (\<lambda>s. h, TS_step_d) (init, h) (as @ x # bs @ x # take i cs))) \<and>
               {xa. xa < cs ! i in fst (config' (\<lambda>s. h, TS_step_d) (init, h) (as @ x # bs @ x # take i cs)) \<and>
                    count_list
                     (take (index (snd (config' (\<lambda>s. h, TS_step_d) (init, h) (as @ x # bs @ x # take i cs))) (cs ! i))
                       (snd (Partial_Cost_Model.config' (\<lambda>s. h, TS_step_d) (init, h) (as @ x # bs @ x # take i cs))))
                     xa
                    \<le> 1} \<noteq>
               {}) = True" using aha[unfolded rTS_def] ss' SS' by(simp add: nth_append)

  have "?s_Suct3 = fst (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (Suc (length as + length bs + i)))))"
    by(auto simp add: s_TS_def)
  also have "\<dots> = step ?s ?y (index ?s ?y - Min (index ?s ` ?S), [])"   
      apply(simp only: once[unfolded assms(1)])
      apply(simp add: Step_def split_def rTS_def del: config'.simps)  
      apply(subst alt_chara) 
      apply(simp only: Let_def )
      apply(simp only: iF)
        by(simp add: nth_append) 
  finally have "?s_Suct3 = step ?s ?y (index ?s ?y - Min (index ?s ` ?S), [])" .
  with isminimal have state_dannach: "?s_Suct3 = step ?s ?y (index ?s ?y - index ?s z, [])" by presburger
    

  \<comment> \<open>so y is moved in front of z, that means:\<close> 
  have yinfrontofz: "?y < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)"
    unfolding   assms(1) state_dannach apply(simp add: step_def del: config'.simps)
    apply(rule mtf2_q_passes)
      using i_in_cs assms(5) apply(simp_all add: s_TS_distinct[unfolded s_TS_def] s_TS_set[unfolded s_TS_def]) 
      using yininit apply(simp)
      using zbeforey_ind by simp 

  
 
           
  have yins: "?y \<in> set ?s"  
      using i_in_cs assms(3,5)  apply(simp_all add:   s_TS_set[unfolded s_TS_def] del: config'.simps) 
      by fastforce

  have "index ?s_Suct3 ?y = index ?s z" 
    and "index ?s_Suct3 z = Suc (index ?s z)" 
    proof -
      let ?xs = "(fst (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (length as + length bs + i)))))"
      have setxs: "set ?xs = set init"
        apply(rule  s_TS_set[unfolded s_TS_def])
          using i_in_cs by auto
      then have yinxs: "cs ! i \<in> set  ?xs"
          apply(simp  add: setxs del: config'.simps) 
          using assms(3) i_in_cs by fastforce
      
      have distinctxs: "distinct ?xs"
        apply(rule  s_TS_distinct[unfolded s_TS_def])
          using i_in_cs assms(5) by auto
      

      let ?n = "(index
             (fst (TSdet init h (as @ x # bs @ x # cs)
                    (Suc (Suc (length as + length bs + i)))))
             (cs ! i) -
            index
             (fst (TSdet init h (as @ x # bs @ x # cs)
                    (Suc (Suc (length as + length bs + i)))))
             z)"
 
      have "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?xs ?y - ?n\<and>
            index ?xs ?y - ?n = index (mtf2 ?n ?y ?xs) (?xs !  index ?xs ?y )"
        apply(rule mtf2_forward_effect2) 
          apply(fact)
          apply(fact)
          by simp
          
      then have  "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?xs ?y - ?n" by metis
      also have "\<dots> = index ?s z" using zbeforey_ind by force
      finally have A: "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?s z" .

      have aa: "index ?xs ?y - ?n \<le> index ?xs z" "index ?xs z < index ?xs ?y" 
        apply(simp)
          using zbeforey_ind by fastforce
 
      from mtf2_forward_effect3'[OF yinxs distinctxs aa] 
        have B: "index (mtf2 ?n ?y ?xs) z = Suc (index ?xs z)" 
          using elemins yins by(simp add: nth_append split_def del: config'.simps)

      show "index ?s_Suct3 ?y = index ?s z" 
        unfolding state_dannach apply(simp add: step_def nth_append del: config'.simps) 
          using A yins by(simp add: nth_append  del: config'.simps)    

      show "index ?s_Suct3 z = Suc (index ?s z)"
        unfolding state_dannach apply(simp add: step_def nth_append del: config'.simps) 
          using B yins by(simp add: nth_append  del: config'.simps)        
  qed
      
  then have are: "Suc (index ?s_Suct3 ?y) = index ?s_Suct3 z" by presburger
        




  from are before_in_def y_before_x_Suct3 el_n_x  assms(1) have z_before_x: "z < x in ?s_Suct3"
    by (metis Suc_lessI not_before_in yinfrontofz) 
 

  have xSuct3: "x\<in>set ?s_Suct3" using assms(4) i_in_cs by(simp add: s_TS_set)
  have elSuct3: "z\<in>set ?s_Suct3" using zininit i_in_cs by(simp add: s_TS_set)

  have xt3: "x\<in>set ?s " apply(subst config_config_set) by fact

  note elt3=elemins

  have z_s: "z < x in ?s"
  proof(rule ccontr, goal_cases)
    case 1
    then have "x < z in ?s" using not_before_in[OF xt3 elt3] el_n_x unfolding s_TS_def by blast
    then have "x < z in ?s_Suct3"
      apply (simp only: state_dannach)
      apply (simp only: step_def)
      apply(simp add: nth_append del: config'.simps)
      apply(rule x_stays_before_y_if_y_not_moved_to_front)
        apply(subst config_config_set) using i_in_cs assms(3) apply fastforce
        apply(subst config_config_distinct) using assms(5) apply fastforce
        apply(subst config_config_set) using assms(4) apply fastforce
        apply(subst config_config_set) using zininit apply fastforce
        using el_n_y apply(simp)
        by(simp)

    then show "False" using z_before_x not_before_in[OF xSuct3 elSuct3] by blast
  qed 


  have mind: "(index ?is (cs ! i)) \<ge> i + 1 + length bs + 1 " using lastoccy 
      using i_in_cs fstTS_t3'[unfolded assms(1)] by(simp add: split_def nth_append del: config'.simps)                    
 
  have "count_list (rev (take i cs) @ [x] @ rev bs @ [x]) z=
      count_list (take (i + 1 + length bs + 1) ?is) z" unfolding is_
        using el_n_x by(simp add: minlencsi count_append ) 
  also from mind have "\<dots> 
          \<le> count_list (take (index ?is (cs ! i)) ?is) z"
          by(rule count_take_less) 
  also have "\<dots> \<le> 1" using zatmostonce by metis
  finally have aaa: "count_list (rev (take i cs) @ [x] @ rev bs @ [x]) z \<le> 1" .
  with el_n_x have "count_list bs z + count_list (take i cs) z \<le> 1"
    by(simp add: count_append count_rev)
  moreover have "count_list (take (Suc i) cs) z = count_list (take i cs) z" 
      using i_in_cs  el_n_y by(simp add: take_Suc_conv_app_nth count_append)
  ultimately have aaaa: "count_list bs z + count_list (take  (Suc i) cs) z \<le> 1" by simp

  have z_occurs_once_in_cs: "count_list (take (Suc i) cs) z = 1"
  proof (rule ccontr, goal_cases)
    case 1
    with aaaa have atmost1: "count_list bs z \<le> 1" and "count_list (take (Suc i) cs) z = 0" by force+
    have yeah: "z \<notin> set (take (Suc i) cs)" apply(rule count_notin2) by fact
 
    \<comment> \<open>now we know that x is in front of z after 2nd request to x, and that z is not requested any more,
        that means it stays behind x, which leads to a contradiction with @{text z_before_x}\<close>

    have xin123: "x \<in> set (s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1)))"
      using i_in_cs assms(4) by(simp add: s_TS_set)
    have zin123: "z \<in> set (s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1)))"  
      using i_in_cs elemins by(simp add: s_TS_set  del: config'.simps)
 
    have "x < z in s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i + 1))"
      apply(rule TS_mono)
        apply(rule xgoestofront)
          apply(fact) using el_n_x apply(simp) apply(fact)
        using i_in_cs apply(simp)
        using yeah i_in_cs length_take  nth_mem
        apply (metis Suc_eq_plus1 Suc_leI min_absorb2)
        using set_take_subset assms(2) apply fast
        using assms i_in_cs  apply(simp_all ) using set_take_subset by fast
    then have ge: "\<not> z < x in s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))"
        using not_before_in[OF zin123 xin123] el_n_x by blast 

        have " s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + (i+1))
          = s_TS init h ((as @ [x] @ bs @ [x] @ (take (i+1) cs)) @ (drop (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))" by auto
        also have "\<dots>
              = s_TS init h (as @ [x] @ bs @ [x] @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))"
              apply(rule s_TS_append)
                using i_in_cs by(simp)
        finally have aaa: " s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + (i+1))
              = s_TS init h (as @ [x] @ bs @ [x] @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))" .

    from ge z_before_x show "False" unfolding assms(1) using aaa by auto 
  qed
  from z_occurs_once_in_cs have kinSuci: "z \<in> set (take (Suc i) cs)" by (metis One_nat_def count_notin n_not_Suc_n)
  then have zincs: "z\<in>set cs" using set_take_subset by fast
  from z_occurs_once_in_cs  obtain k where k_def: "k=index (take (Suc i) cs) z" by blast
 
 
  then have "k=index cs z" using kinSuci by (simp add: index_take_if_set)
  then have zcsk: "z = cs!k" using zincs by simp




   have era: " cs ! index (take (Suc i) cs) z = z" using kinSuci in_set_takeD index_take_if_set by fastforce
   have ki: "k<i" unfolding k_def using kinSuci el_n_y 
    by (metis i_in_cs index_take index_take_if_set le_neq_implies_less not_less_eq_eq yes)
   have zmustbebeforex: "cs!k < x in ?s"
            unfolding k_def era by (fact z_s)
 
  \<comment> \<open>before the request to z, x is in front of z, analog zu oben, vllt generell machen?\<close>


   \<comment> \<open>element z does not occur between t1 and position k\<close>
   have  z_notinbs: "cs ! k \<notin> set bs"
   proof -
      from z_occurs_once_in_cs aaaa have "count_list bs z = 0" by auto
      then show ?thesis using zcsk count_notin2 by metis
   qed

   
   have "count_list bs z \<le> 1" using aaaa by linarith 
   with xgoestofront[OF zininit el_n_x[symmetric]] have xbeforez: "x < z in s_TS init h (as @ [x] @ bs @ [x]) (length (as @ [x] @ bs @ [x]))" by auto

   obtain cs1 cs2 where v: "cs1 @ cs2 = cs" and cs1: "cs1 = take (Suc k) cs" and cs2: "cs2 = drop (Suc k) cs" by auto
  
   have z_firstocc:  "\<forall>j<k.  cs ! j \<noteq> cs ! k"
      and z_lastocc:  "\<forall>j<i-k-1.  cs2 ! j \<noteq> cs ! k" 
   proof (safe, goal_cases)
    case (1 j)  
    with ki i_in_cs have 2: "j < length (take k cs)" by auto
    have un1: "(take (Suc i) cs)!k = cs!k" apply(rule nth_take) using ki by auto
    have un2: "(take k cs)!j = cs!j" apply(rule nth_take) using 1(1) ki by auto

    from i_in_cs ki have f1: "k < length (take (Suc i) cs)" by auto 
    then have "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ (take (Suc i) cs)!k # (drop (Suc k) (take (Suc i) cs))"
      by(rule id_take_nth_drop)
    also have "(take k (take (Suc i) cs)) = take k cs" using i_in_cs ki by (simp add: min_def)
    also have "... = (take j (take k cs)) @ (take k cs)!j # (drop (Suc j) (take k cs))"
        using 2 by(rule id_take_nth_drop)
    finally have "take (Suc i) cs
            =  (take j (take k cs)) @ [(take k cs)!j] @ (drop (Suc j) (take k cs)) 
                        @ [(take (Suc i) cs)!k] @ (drop (Suc k) (take (Suc i) cs))"
                        by(simp)
    then have A: "take (Suc i) cs
            =  (take j (take k cs)) @ [cs!j] @ (drop (Suc j) (take k cs)) 
                        @ [cs!k] @ (drop (Suc k) (take (Suc i) cs))"
                        unfolding un1 un2 by simp
    have "count_list ((take j (take k cs)) @ [cs!j] @ (drop (Suc j) (take k cs)) 
                        @ [cs!k] @ (drop (Suc k) (take (Suc i) cs))) z \<ge> 2"  
                     apply(simp add: count_append)
                      using zcsk 1(2) by(simp)
    with A have "count_list (take (Suc i) cs) z \<ge> 2" by auto
    with z_occurs_once_in_cs show "False" by auto
  next
    case (2 j)
    then have 1: "Suc k+j < i" by auto
    then have f2: "j < length (drop (Suc k) (take (Suc i) cs))" using i_in_cs by simp 
    have 3: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ (drop (Suc k) (take (Suc i) cs))! j
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))"
        using f2 by(rule id_take_nth_drop)
    have "(drop (Suc k) (take (Suc i) cs))! j = (take (Suc i) cs) ! (Suc k+j)"
      apply(rule nth_drop) using i_in_cs 1 by auto
    also have "\<dots> = cs ! (Suc k+j)" apply(rule nth_take) using 1 by auto
    finally have 4: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ cs! (Suc k +j)
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" 
                                         using 3 by auto
    have 5: "cs2 ! j = cs! (Suc k +j)" unfolding cs2
      apply(rule nth_drop) using i_in_cs 1 by auto
    
    from 4 5 2(2) have 6: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ cs! k
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" by auto
                                       
    from i_in_cs ki have 1: "k < length (take (Suc i) cs)" by auto 
    then have 7: "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ (take (Suc i) cs)!k # (drop (Suc k) (take (Suc i) cs))"
      by(rule id_take_nth_drop)
    have 9: "(take (Suc i) cs)!k = z" unfolding zcsk apply(rule nth_take) using ki by auto
    from 6 7 have A: "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ z # take j (drop (Suc k) (take (Suc i) cs))
                                        @ z
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" using ki 9  by auto
    
    have "count_list ((take k (take (Suc i) cs)) @ z # take j (drop (Suc k) (take (Suc i) cs))
                                        @ z
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))) z
                                            \<ge> 2"
                                            by(simp add: count_append)
    with A have "count_list (take (Suc i) cs) z \<ge> 2" by auto
    with z_occurs_once_in_cs show "False" by auto
qed 
 

   have k_in_cs: "k < length cs" using ki i_in_cs by auto
   with cs1 have lenkk: "length cs1 = k+1" by auto
   from k_in_cs have mincsk: "min (length cs) (Suc k) = Suc k" by auto

   have "s_TS init h (((as@[x]@bs@[x])@cs1) @ cs2) (length (as@[x]@bs@[x])+k+1)
        = s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x])+k+1)"
        apply(rule s_TS_append)
          using cs1 cs2 k_in_cs by(simp)
   then have spliter: "s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x]@(cs1)))
        = s_TS init h ((as@[x]@bs@[x])@cs) (length (as@[x]@bs@[x])+k+1) "
          using lenkk v cs1 apply(auto) by (simp add: add.commute add.left_commute)
       
   from cs2 have "length cs2 = length cs - (Suc k)" by auto

   have notxbeforez: "~ x < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + k + 1)"
   proof (rule ccontr, goal_cases)
    case 1 
    then have a: "x < z in s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x]@(cs1)))"
      unfolding spliter assms(1) by auto

    have 41: "x \<in> set(s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + i))"
       using i_in_cs assms(4) by(simp add: s_TS_set)
    have 42: "z \<in> set(s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + i))" 
       using i_in_cs zininit by(simp add: s_TS_set)
     
    have rewr: "s_TS init h ((as@[x]@bs@[x]@cs1)@cs2) (length (as@[x]@bs@[x]@cs1)+(i-k-1)) =
            s_TS init h (as@[x]@bs@[x]@cs) (length (as@[x]@bs@[x])+i)"
            using cs1 v ki  apply(simp add: mincsk) by (simp add: add.commute add.left_commute)

    have "x < z in s_TS init h ((as@[x]@bs@[x]@cs1)@cs2) (length (as@[x]@bs@[x]@cs1)+(i-k-1))"
      apply(rule TS_mono)
        using a apply(simp)
        using cs2 i_in_cs ki v cs1 apply(simp)  
        using z_lastocc zcsk apply(simp)
        using v assms(2) apply force
        using assms by(simp_all add: cs1 cs2)
    
    (* "contradiction to zmustbebeforex" *) 
    from zmustbebeforex this[unfolded rewr ] el_n_x zcsk 41 42 not_before_in show "False"
      unfolding s_TS_def  by fastforce
   qed
       
   have 1: "k < length cs"
                   "(\<forall>j<k. cs ! j \<noteq> cs ! k)"
                   "cs ! k \<noteq> x" "cs ! k \<notin> set bs" 
              "~ x < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + k + 1)"
       apply(safe)
          using ki i_in_cs apply(simp)
          using z_firstocc apply(simp)
          using assms(2) ki i_in_cs apply(fastforce)
          using z_notinbs apply(simp)
          using notxbeforez by auto
          
          
                    
   show ?case apply(simp only: ex_nat_less_eq)
      apply(rule bexI[where x=k])
        using 1 zcsk apply(simp)
        using ki by simp
qed

lemma nopaid: "snd (fst (TS_step_d s q)) = []" unfolding TS_step_d_def by simp

lemma staysuntouched:
   assumes d[simp]: "distinct (fst S)"
    and x: "x \<in> set (fst S)"
    and y: "y \<in> set (fst S)" 
   shows "set qs \<subseteq> set (fst S) \<Longrightarrow> x \<notin> set qs \<Longrightarrow> y \<notin> set qs
        \<Longrightarrow> x < y in fst (config' (rTS []) S qs) =  x < y in fst S" 
proof(induct qs rule: rev_induct)
  case (snoc q qs)
  have "x < y in fst (config' (rTS []) S (qs @ [q])) =
          x < y in fst (config' (rTS []) S qs)"
          apply(simp add: config'_snoc Step_def split_def step_def rTS_def nopaid)
          apply(rule xy_relativorder_mtf2)
            using snoc by(simp_all add: x y )
  also have "\<dots> = x < y in fst S"
    apply(rule snoc)
    using snoc by simp_all
  finally show ?case .
qed simp

lemma staysuntouched':
   assumes d[simp]: "distinct init"
    and x: "x \<in> set init"
    and y: "y \<in> set init"
    and "set qs \<subseteq> set init"
    and "x \<notin> set qs" and "y \<notin> set qs"
   shows "x < y in fst (config (rTS []) init qs) =  x < y in init" 
proof -
  let ?S="(init, fst (rTS []) init)"
  have "x < y in fst (config' (rTS []) ?S qs) =  x < y in fst ?S"
    apply(rule staysuntouched)
      using assms by(simp_all)
  then show ?thesis by simp
qed

lemma projEmpty: "Lxy qs S = [] \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> set qs"
unfolding Lxy_def by (metis filter_empty_conv)  

lemma Lxy_index_mono:
  assumes "x\<in>S" "y\<in>S"
    and "index xs x < index xs y"
    and "index xs y < length xs"
    and "x\<noteq>y"
  shows "index (Lxy xs S) x < index (Lxy xs S) y"
proof -
  from assms have ij: "index xs x < index xs y"
        and xinxs: "index xs x < length xs"
        and yinxs: "index xs y < length xs" by auto  
  then have inset: "x\<in>set xs" "y\<in>set xs" using index_less_size_conv by fast+
  from xinxs obtain a as where dec1: "a @ [xs!index xs x] @ as = xs"
        and a: "a = take (index xs x) xs" and "as = drop (Suc (index xs x)) xs"
        and length_a: "length a = index xs x" and length_as: "length as = length xs - index xs x- 1"
        using id_take_nth_drop by fastforce 
  have "index xs y\<ge>length (a @ [xs!index xs x])" using length_a ij by auto
  then have "((a @ [xs!index xs x]) @ as) ! index xs y = as ! (index xs y-length (a @ [xs ! index xs x]))" using nth_append[where xs="a @ [xs!index xs x]" and ys="as"]
    by(simp)
  then have xsj: "xs ! index xs y = as ! (index xs y-index xs x-1)" using dec1 length_a by auto   
  have las: "(index xs y-index xs x-1) < length as" using length_as yinxs ij by simp
  obtain b c where dec2: "b @ [xs!index xs y] @ c = as"
            and "b = take (index xs y-index xs x-1) as" "c=drop (Suc (index xs y-index xs x-1)) as"
            and length_b: "length b = index xs y-index xs x-1" using id_take_nth_drop[OF las] xsj by force

  have xs_dec: "a @ [xs!index xs x] @ b @ [xs!index xs y] @ c = xs" using dec1 dec2 by auto 
   

  then have "Lxy xs S = Lxy (a @ [xs!index xs x] @ b @ [xs!index xs y] @ c) S"
    by(simp add: xs_dec)
  also have "\<dots> = Lxy a S @ Lxy [x] S @ Lxy b S @ Lxy [y] S @ Lxy c S"
    by(simp add: Lxy_append Lxy_def assms inset)
  finally have gr: "Lxy xs S = Lxy a S @ [x] @ Lxy b S @ [y] @ Lxy c S"
      using assms by(simp add: Lxy_def)

  have "y \<notin> set (take (index xs x) xs)" 
    apply(rule index_take) using assms by simp
  then have "y \<notin>  set (Lxy (take (index xs x) xs) S )"
    apply(subst Lxy_set_filter) by blast
  with a have ynot: "y \<notin> set (Lxy a S)" by simp
  have "index (Lxy xs S) y =
          index (Lxy a S @ [x] @ Lxy b S @ [y] @ Lxy c S) y"
            by(simp add: gr)
  also have "\<dots> \<ge> length (Lxy a S) + 1"
    using assms(5) ynot by(simp add: index_append)
  finally have 1: "index (Lxy xs S) y \<ge> length (Lxy a S) + 1" .

  have "index (Lxy xs S) x = index (Lxy a S @ [x] @ Lxy b S @ [y] @ Lxy c S) x"
    by (simp add: gr)
  also have "\<dots> \<le>  length (Lxy a S)"
    apply(simp add: index_append)
    apply(subst index_less_size_conv[symmetric]) by simp
  finally have 2: "index (Lxy xs S) x \<le> length (Lxy a S)" .

  from 1 2 show ?thesis by linarith
qed

lemma proj_Cons: 
  assumes filterd_cons: "Lxy qs S = a#as"
    and a_filter: "a\<in>S"
  obtains pre suf where "qs = pre @ [a] @ suf" and "\<And>x. x \<in> S \<Longrightarrow> x \<notin> set pre"
                  and "Lxy suf S = as"
proof -
  have "set (Lxy qs S) \<subseteq> set qs" using Lxy_set_filter by fast
  with filterd_cons have a_inq: "a \<in> set qs" by simp
  then have "index qs a < length qs" by(simp)
  { fix e
    assume eS:"e\<in>S"
    assume "e\<noteq>a"
    have "index qs a \<le> index qs e"
    proof (rule ccontr)
      assume "\<not> index qs a \<le> index qs e"
      then have 1: "index qs e < index qs a" by simp
      have 0: "index (Lxy qs S) a = 0" unfolding filterd_cons by simp
      have 2: "index (Lxy qs S) e < index (Lxy qs S) a"
        apply(rule Lxy_index_mono)
          by(fact)+
      from 0 2 show "False" by linarith
    qed
  } note atfront=this


  let ?lastInd="index qs a"
  have "qs = take ?lastInd qs @ qs!?lastInd # drop (Suc ?lastInd) qs"
    apply(rule id_take_nth_drop)
      using a_inq by simp
  also have "\<dots> = take ?lastInd qs @ [a] @ drop (Suc ?lastInd) qs"
    using a_inq by simp
  finally have split: "qs = take ?lastInd qs @ [a] @ drop (Suc ?lastInd) qs" .
  
  have nothingin: "\<And>s. s\<in>S \<Longrightarrow> s \<notin> set (take ?lastInd qs)"
    apply(rule index_take)
    apply(case_tac "a=s")
      apply(simp)
     by (rule atfront) simp_all
  then have "set (Lxy (take ?lastInd qs) S) = {}"
    apply(subst Lxy_set_filter) by blast
  then have emptyPre: "Lxy (take ?lastInd qs) S = []" by blast


  have "a#as = Lxy qs S"
    using filterd_cons by simp
  also have "\<dots> = Lxy (take ?lastInd qs @ [a] @ drop (Suc ?lastInd) qs) S"
    using split by simp
  also have "\<dots> = Lxy (take ?lastInd qs) S @ (Lxy [a] S) @ Lxy (drop (Suc ?lastInd) qs) S"
    by(simp add: Lxy_append Lxy_def)
  also have "\<dots> = a#Lxy (drop (Suc ?lastInd) qs) S"
    unfolding emptyPre by(simp add: Lxy_def a_filter)
  finally have suf: "Lxy (drop (Suc ?lastInd) qs) S = as" by simp
  
  from split nothingin suf show ?thesis ..                          
qed

lemma Lxy_rev: "rev (Lxy qs S) = Lxy (rev qs) S"
apply(induct qs)
  by(simp_all add: Lxy_def)

lemma proj_Snoc: 
  assumes filterd_cons: "Lxy qs S = as@[a]"
    and a_filter: "a\<in>S"
  obtains pre suf where "qs = pre @ [a] @ suf" and "\<And>x. x \<in> S \<Longrightarrow> x \<notin> set suf"
                  and "Lxy pre S = as"
proof - 
  have "Lxy (rev qs) S = rev (Lxy qs S)" by(simp add: Lxy_rev)
  also have "\<dots> = a#(rev as)" unfolding filterd_cons by simp
  finally have "Lxy (rev qs) S = a # (rev as)" .
  with a_filter
  obtain pre' suf' where 1: "rev qs = pre' @[a] @ suf'"
          and 2: "\<And>x. x \<in> S \<Longrightarrow> x \<notin> set pre'"
          and 3: "Lxy suf' S = rev as"
    using proj_Cons by metis
  have "qs = rev (rev qs)" by simp 
  also have "\<dots> = rev suf' @ [a] @ rev pre'" using 1 by simp
  finally have a1: "qs = rev suf' @ [a] @ rev pre'" .

  have "Lxy (rev suf') S = rev (Lxy suf' S)" by(simp add: Lxy_rev)
  also have "\<dots> = as" using 3 by simp
  finally have a3: "Lxy (rev suf') S = as" .

  have a2: "\<And>x. x \<in> S \<Longrightarrow> x \<notin> set (rev pre')" using 2 by simp

  from a1 a2 a3 show ?thesis ..
qed

lemma sndTSconfig': "snd (config' (rTS initH) (init,[]) qs) = rev qs @ []"
apply(induct qs rule: rev_induct)
  apply(simp add: rTS_def)
  by(simp add: split_def TS_step_d_def config'_snoc Step_def rTS_def)

lemma projxx: 
  fixes e a bs
  assumes axy: "a\<in>{x,y}"
  assumes ane: "a\<noteq>e"
  assumes exy: "e\<in>{x,y}"
  assumes add: "f\<in>{[],[e]}" 
  assumes bsaxy: "set (bs @ [a] @ f) \<subseteq> {x,y}"
  assumes Lxyinitxy: "Lxy init {x, y} \<in> {[x,y],[y,x]}"
  shows "a < e in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((bs @ [a] @ f) @ [a]))"
proof -
  have aexy: "{a,e}={x,y}" using exy axy ane by blast

  let ?h="snd (Partial_Cost_Model.config' (\<lambda>s. [], TS_step_d)
                          (Lxy init {x, y}, []) (bs @ a # f))"
  have history: "?h = (rev f)@a#(rev bs)"
    using sndTSdet[of "length (bs@a#f)" "bs@a#f", unfolded rTS_def] by(simp) 
 
  { fix xs s
    assume sinit: "s:{[a,e],[e,a]}"
    assume "set xs \<subseteq> {a,e}"
    then have "fst (config' (\<lambda>s. [], TS_step_d) (s, []) xs) \<in> {[a,e], [e,a]}"
      apply (induct xs rule: rev_induct)
        using sinit apply(simp)                
       apply(subst config'_append2)
       apply(simp only: Step_def config'.simps Let_def split_def fst_conv)
       apply(rule stepxy) by simp_all  
   } note staysae=this

  have opt: "fst (config' (\<lambda>s. [], TS_step_d)
                                       (Lxy init {x, y}, []) (bs @ [a] @ f)) \<in> {[a,e], [e,a]}"
    apply(rule staysae)
      using Lxyinitxy exy axy ane apply fast
      unfolding aexy by(fact bsaxy)

  have contr: " (\<forall>x. 0 < (if e = x then 0 else index [a] x + 1)) = False"
  proof (rule ccontr, goal_cases)
    case 1
    then have "\<And>x. 0 < (if e = x then 0 else index [a] x + 1)" by simp
    then have "0 < (if e = e then 0 else index [a] e + 1)" by blast
    then have "0<0" by simp
    then show "False" by auto
  qed
    

  show "a < e in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((bs @ [a] @ f) @ [a]))"
      apply(subst config_append)
      apply(simp add: rTS_def Step_def split_def)
      apply(subst TS_step_d_def)
      apply(simp only: history)
      using opt ane add
      apply(auto simp: step_def)
           apply(simp add: before_in_def)
          apply(simp add: before_in_def)
         apply(simp add: before_in_def contr)
        apply(simp add: mtf2_def swap_def before_in_def)
       apply(auto simp add: before_in_def contr)
       apply (metis One_nat_def add_is_1 count_list.simps(1) le_Suc_eq)
      by(simp add: mtf2_def swap_def)          
qed

lemma oneposs: 
   assumes "set xs = {x,y}"
      assumes "x\<noteq>y"
      assumes "distinct xs"
      assumes True: "x<y in xs"
      shows "xs = [x,y]"
proof -
  from assms have len2: "length xs = 2" using distinct_card[OF assms(3)] by fastforce
  from True have "index xs x < index xs y" "index xs y < length xs" unfolding before_in_def using assms
        by simp_all
  then have f: "index xs x = 0 \<and> index xs y = 1" using len2 by linarith
  have "xs = take 1 xs @ xs!1 # drop (Suc 1) xs"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = take 1 xs @ [xs!1]" using len2 by simp
  also have "take 1 xs = take 0 (take 1 xs) @ (take 1 xs)!0 # drop (Suc 0) (take 1 xs)"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = [xs!0]" by(simp)
  finally have "xs = [xs!0, xs!1]" by simp
  also have "\<dots> = [xs!(index xs x), xs!index xs y]" using f by simp
  also have "\<dots> = [x,y]" using assms by(simp) 
  finally show "xs = [x,y]" . 
qed

lemma twoposs: 
   assumes "set xs = {x,y}"
      assumes "x\<noteq>y"
      assumes "distinct xs"
      shows "xs \<in> {[x,y], [y,x]}"
proof (cases "x<y in xs")
  case True
  from assms have len2: "length xs = 2" using distinct_card[OF assms(3)] by fastforce
  from True have "index xs x < index xs y" "index xs y < length xs" unfolding before_in_def using assms
        by simp_all
  then have f: "index xs x = 0 \<and> index xs y = 1" using len2 by linarith
  have "xs = take 1 xs @ xs!1 # drop (Suc 1) xs"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = take 1 xs @ [xs!1]" using len2 by simp
  also have "take 1 xs = take 0 (take 1 xs) @ (take 1 xs)!0 # drop (Suc 0) (take 1 xs)"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = [xs!0]" by(simp)
  finally have "xs = [xs!0, xs!1]" by simp
  also have "\<dots> = [xs!(index xs x), xs!index xs y]" using f by simp
  also have "\<dots> = [x,y]" using assms by(simp) 
  finally have "xs = [x,y]" .
  then show ?thesis by simp
next
  case False
  from assms have len2: "length xs = 2" using distinct_card[OF assms(3)] by fastforce
  from False have "y<x in xs" using not_before_in assms(1,2) by fastforce
  then have "index xs y < index xs x" "index xs x < length xs" unfolding before_in_def using assms
        by simp_all
  then have f: "index xs y = 0 \<and> index xs x = 1" using len2 by linarith
  have "xs = take 1 xs @ xs!1 # drop (Suc 1) xs"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = take 1 xs @ [xs!1]" using len2 by simp
  also have "take 1 xs = take 0 (take 1 xs) @ (take 1 xs)!0 # drop (Suc 0) (take 1 xs)"
    apply(rule id_take_nth_drop) using len2 by simp
  also have "\<dots> = [xs!0]" by(simp)
  finally have "xs = [xs!0, xs!1]" by simp
  also have "\<dots> = [xs!(index xs y), xs!index xs x]" using f by simp
  also have "\<dots> = [y,x]" using assms by(simp) 
  finally have "xs = [y,x]" .
  then show ?thesis by simp
qed

lemma TS_pairwise': assumes "qs \<in> {xs. set xs \<subseteq> set init}"
       "(x, y) \<in> {(x, y). x \<in> set init \<and> y \<in> set init \<and> x \<noteq> y}"
       "x \<noteq> y" "distinct init"
   shows "Pbefore_in x y (embed (rTS [])) qs init =
       Pbefore_in x y (embed (rTS [])) (Lxy qs {x, y}) (Lxy init {x, y})"
proof -
  from assms have xyininit: "{x, y} \<subseteq> set init" 
        and qsininit: "set qs \<subseteq> set init" by auto
  note dinit=assms(4)
  from assms have xny: "x\<noteq>y" by simp
  have Lxyinitxy: "Lxy init {x, y} \<in> {[x, y], [y, x]}"
    apply(rule twoposs)
      apply(subst Lxy_set_filter) using xyininit apply fast
      using xny Lxy_distinct[OF dinit] by simp_all
                              
  have lq_s: "set (Lxy qs {x, y}) \<subseteq> {x,y}" by (simp add: Lxy_set_filter)
 
  (* projected history *)
  let ?pH = "snd (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
  have "?pH =snd (TSdet (Lxy init {x, y}) [] (Lxy qs {x, y}) (length (Lxy qs {x, y})))"
    by(simp)
  also have "\<dots> = rev (take (length (Lxy qs {x, y})) (Lxy qs {x, y})) @ []"
    apply(rule sndTSdet) by simp
  finally have pH: "?pH = rev (Lxy qs {x, y})" by simp

  let ?pQs = "(Lxy qs {x, y})"

  have A: " x < y in fst (config\<^sub>p (rTS []) init qs)
      =   x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
  proof(cases "?pQs" rule: rev_cases)
    case Nil
    then have xqs: "x \<notin> set qs" and yqs: "y \<notin> set qs" by(simp_all add: projEmpty) 
    have " x < y in fst (config\<^sub>p (rTS []) init qs)
          =  x < y in init" apply(rule staysuntouched') using assms xqs yqs by(simp_all)
    also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
      unfolding Nil apply(simp) apply(rule Lxy_mono) using xyininit dinit by(simp_all)
    finally show ?thesis .
  next
    case (snoc as a)  
    then have "a\<in>set (Lxy qs {x, y})" by (simp)
    then have axy: "a\<in>{x,y}" by(simp add: Lxy_set_filter)
    with xyininit have ainit: "a\<in>set init" by auto
    note a=snoc
    from a axy obtain pre suf  where qs: "qs = pre @ [a] @ suf"
                  and nosuf: "\<And>e. e \<in> {x,y} \<Longrightarrow> e \<notin> set suf" 
                  and pre: "Lxy pre {x,y} = as"
          using proj_Snoc by metis
    show ?thesis
    proof (cases "as" rule: rev_cases)
      case Nil  
      from pre Nil have xqs: "x \<notin> set pre" and yqs: "y \<notin> set pre" by(simp_all add: projEmpty) 
      from xqs yqs axy have "a \<notin> set pre" by blast
      then have noocc: "index (rev pre) a = length (rev pre)" by simp
      have " x < y in fst (config\<^sub>p (rTS []) init qs)
            =  x < y in fst (config\<^sub>p (rTS []) init ((pre @ [a]) @ suf))" by(simp add: qs)
      also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init (pre @ [a]))"
        apply(subst config_append)
        apply(rule staysuntouched) using assms xqs yqs qs nosuf by(simp_all)
      also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init pre)"
        apply(subst config_append)
        apply(simp add: rTS_def Step_def split_def)
        apply(simp only: TS_step_d_def)
        apply(simp only: sndTSconfig'[unfolded rTS_def])
        by(simp add: noocc step_def)
      also have "\<dots> = x < y in init"
        apply(rule staysuntouched') using assms xqs yqs qs by(simp_all)        
      also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
        unfolding a Nil apply(simp add: Step_def split_def rTS_def TS_step_d_def step_def)
          apply(rule Lxy_mono) using xyininit dinit by(simp_all)
      finally show ?thesis .
    next
      case (snoc bs b) 
      note b=this
      with a have "b\<in>set (Lxy qs {x, y})" by (simp)
      then have bxy: "b\<in>{x,y}" by(simp add: Lxy_set_filter)
      with xyininit have binit: "b\<in>set init" by auto
      from b pre have "Lxy pre {x,y} = bs @ [b]" by simp
      with bxy obtain pre2 suf2  where bs: "pre = pre2 @ [b] @ suf2"
                    and nosuf2: "\<And>e. e \<in> {x,y} \<Longrightarrow> e \<notin> set suf2" 
                    and pre2: "Lxy pre2 {x,y} = bs"
            using proj_Snoc by metis

      from bs qs have qs2: "qs = pre2 @ [b] @ suf2 @ [a] @ suf" by simp
      
      show ?thesis
      proof (cases "a=b")
        case True
        note ab=this 
 
        let ?qs ="(pre2 @ [a] @ suf2 @ [a]) @ suf"
        {
          fix e
          assume ane: "a\<noteq>e"
          assume exy: "e\<in>{x,y}"
          have "a < e in fst (config\<^sub>p (rTS []) init qs)
              = a < e in fst (config\<^sub>p (rTS []) init ?qs)" using True qs2 by(simp)
          also have "\<dots> = a < e in fst  (config\<^sub>p (rTS []) init (pre2 @ [a] @ suf2 @ [a]))"
            apply(subst config_append)
            apply(rule staysuntouched) using assms qs nosuf apply(simp_all)
              using  exy xyininit apply fast
              using nosuf axy apply(simp)
              using nosuf exy by simp
          also have "\<dots>"
            apply(simp)
            apply(rule twotox[unfolded s_TS_def, simplified])
              using nosuf2 exy apply(simp)
              using assms  apply(simp_all)
              using axy xyininit  apply fast
              using exy xyininit  apply fast
              using nosuf2 axy apply(simp)
              using ane by simp
          finally have "a < e in fst (config\<^sub>p (rTS []) init qs)" by simp
        } note full=this 
   
        have "set (bs @ [a]) \<subseteq> set (Lxy qs {x, y})" using a b  by auto
        also have "\<dots> = {x,y} \<inter> set qs" by (rule Lxy_set_filter)
        also have "\<dots> \<subseteq> {x,y}" by simp
        finally have bsaxy: "set (bs @ [a]) \<subseteq> {x,y}" .

        with xny show ?thesis
        proof(cases "x=a")
          case True
          have 1: "a < y in fst (config\<^sub>p (rTS []) init qs)"
            apply(rule full)
              using True xny apply blast
              by simp


          have "a < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))
              = a < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((bs @ [a] @ []) @ [a]))"
              using a b ab by simp
          also have "\<dots>"
            apply(rule projxx[where bs=bs and f="[]"])
              using True apply blast
              using a b True ab xny Lxyinitxy bsaxy by(simp_all) 
          finally show ?thesis using True 1 by simp
        next
          case False
          with axy have ay: "a=y" by blast
          have 1: "a < x in fst (config\<^sub>p (rTS []) init qs)"
            apply(rule full)
              using False xny apply blast
              by simp
          have "a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))
              = a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((bs @ [a] @ []) @ [a]))"
              using a b ab by simp
          also have "\<dots>"
            apply(rule projxx[where bs=bs and f="[]"])
              using True axy apply blast
              using a b True ab xny Lxyinitxy ay bsaxy by(simp_all)
          finally have 2: "a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))" .

          have "x < y in fst (config\<^sub>p (rTS []) init qs) = 
             (\<not> y < x in fst (config\<^sub>p (rTS []) init qs))"
            apply(subst not_before_in)
              using assms by(simp_all)
          also have "\<dots> = False" using  1 ay by simp
          also have "\<dots> = (\<not> y < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y})))"
            using 2 ay by simp
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
            apply(subst not_before_in)
              using assms  by(simp_all add: Lxy_set_filter)
          finally show ?thesis .
        qed
      next
        case False
        note ab=this

        show ?thesis
        proof (cases "bs" rule: rev_cases)
          case Nil
          with a b have "Lxy qs {x, y} = [b,a]" by simp
          from pre2 Nil have xqs: "x \<notin> set pre2" and yqs: "y \<notin> set pre2" by(simp_all add: projEmpty) 
          from xqs yqs bxy have "b \<notin> set pre2" by blast
          then have noocc2: "index (rev pre2) b = length (rev pre2)" by simp 
          from axy nosuf2 have "a \<notin> set suf2" by blast
          with xqs yqs axy False have "a \<notin> set ((pre2 @ b # suf2))" by(auto)
          then have noocc: "index (rev (pre2 @ b # suf2) @ []) a = length (rev (pre2 @ b # suf2))" by simp
          have " x < y in fst (config\<^sub>p (rTS []) init qs)
                =  x < y in fst (config\<^sub>p (rTS []) init ((((pre2 @ [b]) @ suf2) @ [a]) @ suf))" by(simp add: qs2)
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init (((pre2 @ [b]) @ suf2) @ [a]))"
            apply(subst config_append)
            apply(rule staysuntouched) using assms xqs yqs qs nosuf by(simp_all)
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init ((pre2 @ [b]) @ suf2))"
            apply(subst config_append)
            apply(simp add: rTS_def Step_def split_def)
            apply(simp only: TS_step_d_def)
            apply(simp only: sndTSconfig'[unfolded rTS_def])
            apply(simp only: noocc) by (simp add: step_def)
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init (pre2 @ [b]))"
            apply(subst config_append)
            apply(rule staysuntouched) using assms xqs yqs qs2 nosuf2 by(simp_all)
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) init (pre2))"
            apply(subst config_append)
            apply(simp add: rTS_def Step_def split_def)
            apply(simp only: TS_step_d_def)
            apply(simp only: sndTSconfig'[unfolded rTS_def])
            by(simp add: noocc2 step_def)
          also have "\<dots> = x < y in init"
            apply(rule staysuntouched') using assms xqs yqs qs2 by(simp_all)        
          also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
            unfolding a b Nil
            using False
            apply(simp add: Step_def split_def rTS_def TS_step_d_def step_def) 
              apply(rule Lxy_mono) using xyininit dinit by(simp_all)
          finally show ?thesis . 
        next
          case (snoc cs c)   
          note c=this
          with a b have "c\<in>set (Lxy qs {x, y})" by (simp)
          then have cxy: "c\<in>{x,y}" by(simp add: Lxy_set_filter)
          from c pre2 have "Lxy pre2 {x,y} = cs @ [c]" by simp
          with cxy obtain pre3 suf3  where cs: "pre2 = pre3 @ [c] @ suf3"
                        and nosuf3: "\<And>e. e \<in> {x,y} \<Longrightarrow> e \<notin> set suf3" 
                        and pre3: "Lxy pre3 {x,y} = cs"
                using proj_Snoc by metis    

          let ?qs=" pre3 @ [c] @ suf3 @ [b] @ suf2 @ [a] @ suf"
          from bs cs qs have qs2: "qs = ?qs" by simp
                   
          show ?thesis
          proof(cases "c=a")
            case True (* aba *)
            note ca=this
 
            have "a < b in fst (config\<^sub>p (rTS []) init qs)
                = a < b in fst (config\<^sub>p (rTS []) init ((pre3 @ a # (suf3 @ [b] @ suf2) @ [a]) @ suf))"
                  using qs2 True by simp
            also have "\<dots> = a < b in fst (config\<^sub>p (rTS []) init (pre3 @ a # (suf3 @ [b] @ suf2) @ [a]))"
              apply(subst config_append)
              apply(rule staysuntouched) using assms qs nosuf apply(simp_all)
                using bxy xyininit apply(fast)
                using nosuf axy bxy by(simp_all)
            also have "..."
              apply(rule twotox[unfolded s_TS_def, simplified])
                using nosuf2 nosuf3 bxy apply(simp add: count_append)
                using assms apply(simp_all)
                using axy xyininit apply(fast)
                using bxy xyininit apply(fast)
                using ab nosuf2 nosuf3 axy apply(simp)
                using ab by simp
            finally have full: "a < b in fst (config\<^sub>p (rTS []) init qs)" by simp
  

            have "set (cs @ [a] @ [b]) \<subseteq> set (Lxy qs {x, y})" using a b c  by auto
            also have "\<dots> = {x,y} \<inter> set qs" by (rule Lxy_set_filter)
            also have "\<dots> \<subseteq> {x,y}" by simp
            finally have csabxy: "set (cs @ [a] @ [b]) \<subseteq> {x,y}" .

            with xny show ?thesis
            proof(cases "x=a")
              case True
              with xny ab bxy have bisy: "b=y" by blast
              have 1: "x < y in fst (config\<^sub>p (rTS []) init qs)"
                using full True bisy by simp

              have "a < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))
                  = a < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((cs @ [a] @ [b]) @ [a]))"
                  using a b c ca ab by simp
              also have "\<dots>"
                apply(rule projxx)
                  using True apply blast
                  using a b True ab xny Lxyinitxy csabxy by(simp_all) 
              finally show ?thesis using 1 True by simp
            next
              case False
              with axy have ay: "a=y" by blast
              with xny ab bxy have bisx: "b=x" by blast
              have 1: "y < x in fst (config\<^sub>p (rTS []) init qs)"
                using full ay bisx by simp

              have "a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))
                  = a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) ((cs @ [a] @ [b]) @ [a]))"
                  using a b c ca ab by simp
              also have "\<dots>"
                apply(rule projxx) 
                  using a b True ab xny Lxyinitxy csabxy False by(simp_all) 
              finally have 2: "a < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))" .
    
              have "x < y in fst (config\<^sub>p (rTS []) init qs) = 
                 (\<not> y < x in fst (config\<^sub>p (rTS []) init qs))"
                apply(subst not_before_in)
                  using assms by(simp_all)
              also have "\<dots> = False" using  1 ay by simp
              also have "\<dots> = (\<not> y < x in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y})))"
                using 2 ay by simp
              also have "\<dots> = x < y in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
                apply(subst not_before_in)
                  using assms  by(simp_all add: Lxy_set_filter)
              finally show ?thesis .
            qed
          next
            case False  (* bba *)
            then have cb: "c=b" using bxy cxy axy ab by blast
            
            let ?cs = "suf2 @ [a] @ suf"
            let ?i = "index ?cs a"


            have aed: "(\<forall>j<index (suf2 @ a # suf) a. (suf2 @ a # suf) ! j \<noteq> a)"
              by (metis add.right_neutral axy index_Cons index_append nosuf2 nth_append nth_mem)
 
            have "?i < length ?cs      
              \<longrightarrow> (\<forall>j<?i. ?cs ! j \<noteq> ?cs ! ?i) \<longrightarrow> ?cs ! ?i \<noteq> b
                \<longrightarrow> ?cs ! ?i \<notin> set suf3
                \<longrightarrow> b < ?cs ! ?i in s_TS init [] qs (length (pre3 @ [b] @ suf3 @ [b]) + ?i + 1)"
              apply(rule casexxy) 
                     using cb qs2 apply(simp)
                    using bxy ab nosuf2 nosuf apply(simp)
                   using bs qs qsininit apply(simp)
                  using bxy xyininit apply(blast)
                 apply(fact)
                using nosuf3 bxy apply(simp)
              using cs bs qs qsininit by(simp_all)
                
            then have inner: "b < a in s_TS init [] qs (length (pre3 @ [b] @ suf3 @ [b]) + ?i + 1)"
              using ab nosuf3 axy bxy aed
              by(simp) 
            let ?n = "(length (pre3 @ [b] @ suf3 @ [b]) + ?i + 1)"
            let ?inner="(config\<^sub>p (rTS []) init (take (length (pre3 @ [b] @ suf3 @ [b]) + ?i + 1) ?qs))"

            have "b < a in fst (config\<^sub>p (rTS []) init qs)
              = b < a in fst (config\<^sub>p (rTS []) init (take ?n ?qs @ drop ?n ?qs))" using qs2 by simp
            also have "\<dots> = b < a in fst (config' (rTS []) ?inner suf)" apply(simp only: config_append drop_append) 
              using nosuf2 axy by(simp add: index_append config_append)
            also have "\<dots> = b < a in fst ?inner" 
              apply(rule staysuntouched) using assms bxy xyininit  qs nosuf apply(simp_all)
              using bxy xyininit apply(blast)
              using axy xyininit by (blast)
            also have "\<dots> = True" using inner by(simp add: s_TS_def qs2)
            finally have full: "b < a in fst (config\<^sub>p (rTS []) init qs)" by simp
               
            have "set (cs @ [b] @ []) \<subseteq> set (Lxy qs {x, y})" using a b c  by auto
            also have "\<dots> = {x,y} \<inter> set qs" by (rule Lxy_set_filter)
            also have "\<dots> \<subseteq> {x,y}" by simp
            finally have csbxy: "set (cs @ [b] @ []) \<subseteq> {x,y}" .
 
            have "set (Lxy init {x, y}) = {x,y} \<inter> set init"
              by(rule Lxy_set_filter)
            also have "\<dots> = {x,y}" using xyininit by fast
            also have "\<dots> = {b,a}" using axy bxy ab by fast
            finally have r: "set (Lxy init {x, y}) = {b, a}" .

            let ?confbef="(config\<^sub>p (rTS []) (Lxy init {x, y}) ((cs @ [b] @ []) @ [b]))"
            have f1: "b < a in fst ?confbef"
              apply(rule projxx)
                using bxy ab axy a b c csbxy Lxyinitxy by(simp_all)
            have 1: "fst ?confbef = [b,a]" 
              apply(rule oneposs)
                using ab axy bxy xyininit Lxy_distinct[OF dinit] f1 r by(simp_all)
            have 2: "snd (Partial_Cost_Model.config'
                           (\<lambda>s. [], TS_step_d)
                           (Lxy init {x, y}, [])
                           (cs @ [b, b])) = [b,b]@(rev cs)" 
              using sndTSdet[of "length (cs @ [b, b])" "(cs @ [b, b])", unfolded rTS_def] by(simp) 
            have "b < a in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))
              = b < a in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (((cs @ [b] @ []) @ [b])@[a]))"
              using a b c cb by(simp)
            also have "\<dots>"
              apply(subst config_append)
              using 1 2 ab apply(simp add: step_def Step_def split_def rTS_def TS_step_d_def)
                by(simp add: before_in_def) 
            finally have projected: "b < a in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))" .


            have 1: "{x,y} = {a,b}" using ab axy bxy by fast
            with xny show ?thesis
            proof(cases "x=a")
              case True
              with 1 xny have y: "y=b" by fast
              have "a < b in fst (config\<^sub>p (rTS []) init qs) = 
                 (\<not> b < a in fst (config\<^sub>p (rTS []) init qs))"
                apply(subst not_before_in)
                  using binit ainit ab by(simp_all)
              also have "\<dots> = False" using  full by simp
              also have "\<dots> = (\<not> b < a in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y})))"
                using projected by simp
              also have "\<dots> = a < b in fst (config\<^sub>p (rTS []) (Lxy init {x, y}) (Lxy qs {x, y}))"
                apply(subst not_before_in)
                  using binit ainit ab axy bxy  by(simp_all add: Lxy_set_filter)
              finally show ?thesis using True y by simp
            next
              case False
              with 1 xny have y: "y=a" "x=b" by fast+
              with full projected show ?thesis by fast
            qed
          qed (* end of (c=a) *)
        qed (* end of snoc cs c *)
      qed (* end of (a=b) *)
    qed (* end snoc bs b *)
  qed (* end snoc as a *)

        


  show ?thesis unfolding Pbefore_in_def
    apply(subst config_embed)
    apply(subst config_embed)
      apply(simp) by (rule A) 
qed

theorem TS_pairwise: "pairwise (embed (rTS []))"
apply(rule pairwise_property_lemma)
  apply(rule TS_pairwise') by (simp_all add: rTS_def TS_step_d_def)


subsection "TS is 2-compet"


lemma TS_compet':   "pairwise (embed (rTS [])) \<Longrightarrow> 
      \<forall>s0\<in>{init::(nat list). distinct init \<and> init\<noteq>[]}. \<exists>b\<ge>0. \<forall>qs\<in>{x. set x \<subseteq> set s0}. T\<^sub>p_on_rand (embed (rTS [])) s0 qs \<le> (2::real) *  T\<^sub>p_opt s0 qs + b"
unfolding rTS_def 
proof (rule factoringlemma_withconstant, goal_cases)
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
            
            { fix a::nat
              fix b::nat
              fix qs
              assume as: "a \<noteq> b" "set qs \<subseteq> {a, b}"
              have "T_on_rand' (embed (rTS [])) (fst (embed (rTS [])) [a,b] \<bind> (\<lambda>is. return_pmf ([a,b], is))) qs
                    = T\<^sub>p_on (rTS []) [a, b] qs" by (rule  T_on_embed[symmetric])
              also from as have "\<dots> \<le> 2 * T\<^sub>p_opt [a, b] qs + 2" using TS_OPT2' by fastforce 
              finally have "T_on_rand' (embed (rTS [])) (fst (embed (rTS [])) [a,b] \<bind> (\<lambda>is. return_pmf ([a,b], is))) qs
                    \<le> 2 * T\<^sub>p_opt [a, b] qs + 2"  .
            } note ye=this

            show ?case
              apply(cases "(Lxy init {a, b}) = [a,b]")  
                using ye[OF a b1, unfolded rTS_def] apply(simp)
                using pos ye[OF a[symmetric] b2, unfolded rTS_def] by(simp add: twist) 
          qed
    qed
next
  case 6
  show ?case unfolding TS_step_d_def by (simp add: split_def TS_step_d_def)
next
  case (7 init qs x) 
  then show ?case
    apply(induct x) 
      by (simp_all add: rTS_def split_def take_Suc_conv_app_nth config'_rand_snoc ) 
next
  case 4 then show ?case by simp
qed (simp_all)
 

lemma TS_compet: "compet_rand (embed (rTS [])) 2 {init. distinct init \<and> init \<noteq> []}"
unfolding compet_rand_def static_def
using TS_compet'[OF TS_pairwise] by simp
 
end
