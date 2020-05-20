(*<*)
(*
   Title:  Theory SteamBoiler_proof.thy (Steam Boiler System: Verification)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)
section \<open>Steam Boiler System: Verification\<close>

theory  SteamBoiler_proof 
imports SteamBoiler
begin

subsection \<open>Properties of the Boiler Component\<close>

lemma L1_Boiler:
  assumes "SteamBoiler x s y"
         and "ts x"
  shows "ts s"
using assms  by (simp add: SteamBoiler_def)

lemma L2_Boiler:
  assumes "SteamBoiler x s y"
         and "ts x"
  shows "ts y"
using assms  by (simp add: SteamBoiler_def) 

lemma L3_Boiler:
  assumes "SteamBoiler x s y"
         and "ts x" 
  shows "200 \<le> hd (s 0)"
using assms by (simp add: SteamBoiler_def)

lemma L4_Boiler:
  assumes "SteamBoiler x s y"
         and "ts x" 
  shows "hd (s 0) \<le> 800"
using assms by (simp add: SteamBoiler_def)

lemma L5_Boiler:
  assumes h1:"SteamBoiler x s y"
         and h2:"ts x" 
         and h3:"hd (x j) = Zero"
  shows "(hd (s j)) \<le> hd (s (Suc j)) + (10::nat)"
proof -  
   from h1 and h2 obtain r where
     a1:"r \<le> 10"  and
     a2:"hd (s (Suc j)) = (if hd (x j) = Zero then hd (s j) - r else hd (s j) + r)" 
     by (simp add: SteamBoiler_def, auto)
   from a2 and h3 have "hd (s (Suc j)) = hd (s j) - r" by simp
   from this and a1 show ?thesis by auto
qed

lemma L6_Boiler:
  assumes h1:"SteamBoiler x s y"
         and h2:"ts x" 
         and h3:"hd (x j) = Zero"
  shows "(hd (s j)) - (10::nat) \<le> hd (s (Suc j))" 
proof -  
   from h1 and h2 obtain r where
     a1:"r \<le> 10"  and
     a2:"hd (s (Suc j)) = (if hd (x j) = Zero then hd (s j) - r else hd (s j) + r)" 
     by (simp add: SteamBoiler_def, auto)
   from a2 and h3 have "hd (s (Suc j)) = hd (s j) - r" by simp
   from this and a1 show ?thesis by auto
qed

lemma L7_Boiler:
  assumes h1:"SteamBoiler x s y"
      and h2:"ts x" 
      and h3:"hd (x j) \<noteq> Zero"
  shows "(hd (s j)) \<ge> hd (s (Suc j)) - (10::nat)" 
proof -  
   from h1 and h2 obtain r where
     a1:"r \<le> 10"  and
     a2:"hd (s (Suc j)) = (if hd (x j) = Zero then hd (s j) - r else hd (s j) + r)" 
     by (simp add: SteamBoiler_def, auto)
   from a2 and h3 have "hd (s (Suc j)) = hd (s j) + r" by simp
   from this and a1 show ?thesis by auto
qed

lemma L8_Boiler:
  assumes h1:"SteamBoiler x s y"
         and h2:"ts x" 
         and h3:"hd (x j) \<noteq> Zero"
  shows "(hd (s j)) + (10::nat) \<ge> hd (s (Suc j))" 
proof -  
   from h1 and h2 obtain r where
     a1:"r \<le> 10"  and
     a2:"hd (s (Suc j)) = (if hd (x j) = Zero then hd (s j) - r else hd (s j) + r)" 
     by (simp add: SteamBoiler_def, auto)
   from a2 and h3 have "hd (s (Suc j)) = hd (s j) + r" by simp
   from this and a1 show ?thesis by auto
qed


subsection \<open>Properties of the Controller Component\<close>

lemma L1_Controller:
  assumes "Controller_L s (fin_inf_append [Zero] l) l z"
  shows    "fin_make_untimed (inf_truncate z i) \<noteq> []"
using assms
by (metis Controller_L_def fin_make_untimed_inf_truncate_Nonempty_all0a)

lemma L2_Controller_Zero:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "l t = Zero"
         and "300 < hd (y (Suc t))"
  shows    "z (Suc t) = []"
using assms
by (metis Controller_L_def correct_fin_inf_append1)

lemma L2_Controller_One:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
          and "l t = One"
          and "hd (y (Suc t)) < 700"
  shows "z (Suc t) = []"
using assms
by (metis Controller_L_def bit.distinct(1) correct_fin_inf_append2)

lemma L3_Controller_Zero:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "l t = Zero"
         and "\<not> 300 < hd (y (Suc t))"
  shows "z (Suc t) = [One]"
using assms
by (metis Controller_L_def correct_fin_inf_append1)

lemma L3_Controller_One:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
      and "l t = One"
      and "\<not> hd (y (Suc t)) < 700"
  shows      "z (Suc t) = [Zero]"
using assms
by (metis Controller_L_def bit.distinct(1) correct_fin_inf_append1)

lemma L4_Controller_Zero:
  assumes h1:"Controller_L y (fin_inf_append [Zero] l) l z"
         and h2:"l (Suc t) = Zero" 
  shows      "(z (Suc t) = [] \<and> l t = Zero) \<or> (z (Suc t) = [Zero] \<and> l t = One)"
proof (cases "l t")
  assume a1:"l t = Zero"
  from this and h1 and h2 show ?thesis
  proof -
    from a1 have sg1:"fin_inf_append [Zero] l (Suc t) = Zero"
      by (simp add: correct_fin_inf_append1)
    from h1 and sg1 have sg2:
      "if 300 < hd (y (Suc t)) 
       then z (Suc t) = [] \<and> l (Suc t) = Zero 
       else z (Suc t) = [One] \<and> l (Suc t) = One"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "300 < hd (y (Suc t))")
      assume a11:"300 < hd (y (Suc t))"
      from a11 and sg2 have sg3:"z (Suc t) = [] \<and> l (Suc t) = Zero" by simp
      from this and a1 show ?thesis by simp
    next
      assume a12:"\<not> 300 < hd (y (Suc t))"
      from a12 and sg2 have sg4:"z (Suc t) = [One] \<and> l (Suc t) = One" by simp
      from this and h2 show ?thesis by simp
    qed
  qed
next
  assume a2:"l t = One"
  from this and h1 and h2 show ?thesis
  proof -
    from a2 have sg5:"fin_inf_append [Zero] l (Suc t) \<noteq> Zero"
      by (simp add: correct_fin_inf_append1)
    from h1 and sg5 have sg6:
      "if hd (y (Suc t)) < 700 
       then z (Suc t) = [] \<and> l (Suc t) = One 
       else z (Suc t) = [Zero] \<and> l (Suc t) = Zero"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "hd (y (Suc t)) < 700")
      assume a21:"hd (y (Suc t)) < 700"
      from a21 and sg6 have sg7:"z (Suc t) = [] \<and> l (Suc t) = One" by simp
      from this and h2 show ?thesis by simp
    next 
      assume a22:"\<not> hd (y (Suc t)) < 700"
      from a22 and sg6 have sg8:"z (Suc t) = [Zero] \<and> l (Suc t) = Zero" by simp
      from this and a2 show ?thesis by simp
    qed
  qed
qed


lemma L4_Controller_One:
  assumes h1:"Controller_L y (fin_inf_append [Zero] l) l z"
      and h2:"l (Suc t) = One" 
  shows      "(z (Suc t) = [] \<and> l t = One) \<or> (z (Suc t) = [One] \<and> l t = Zero)"
proof (cases "l t")
  assume a1:"l t = Zero"
  from this and h1 and h2 show ?thesis
  proof -
    from a1 have sg1:"fin_inf_append [Zero] l (Suc t) = Zero"
      by (simp add: correct_fin_inf_append1)
    from h1 and sg1 have sg2:
      "if 300 < hd (y (Suc t)) 
       then z (Suc t) = [] \<and> l (Suc t) = Zero 
       else z (Suc t) = [One] \<and> l (Suc t) = One"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "300 < hd (y (Suc t))")
      assume a11:"300 < hd (y (Suc t))"
      from a11 and sg2 have sg3:"z (Suc t) = [] \<and> l (Suc t) = Zero" by simp
      from this and h2 show ?thesis by simp
    next
      assume a12:"\<not> 300 < hd (y (Suc t))"
      from a12 and sg2 have sg4:"z (Suc t) = [One] \<and> l (Suc t) = One" by simp
      from this and a1 show ?thesis by simp
    qed
  qed
next
  assume a2:"l t = One"
  from this and h1 and h2 show ?thesis
  proof -
    from a2 have sg5:"fin_inf_append [Zero] l (Suc t) \<noteq> Zero"
      by (simp add: correct_fin_inf_append1)
    from h1 and sg5 have sg6:
      "if hd (y (Suc t)) < 700 
       then z (Suc t) = [] \<and> l (Suc t) = One 
       else z (Suc t) = [Zero] \<and> l (Suc t) = Zero"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "hd (y (Suc t)) < 700")
      assume a21:"hd (y (Suc t)) < 700"
      from a21 and sg6 have sg7:"z (Suc t) = [] \<and> l (Suc t) = One" by simp
      from this and a2 show ?thesis by simp
    next 
      assume a22:"\<not> hd (y (Suc t)) < 700"
      from a22 and sg6 have sg8:"z (Suc t) = [Zero] \<and> l (Suc t) = Zero" by simp
      from this and h2 show ?thesis by simp
    qed
  qed
qed

lemma L5_Controller_Zero:
  assumes h1:"Controller_L y lIn lOut z"
      and h2:"lOut t = Zero"
      and h3:"z t = []"
  shows "lIn t = Zero" 
proof (cases "lIn t")
  assume a1:"lIn t = Zero"
  from this show ?thesis by simp 
next
  assume a2:"lIn t = One"
  from a2 and h1 have sg1:
    "if hd (y t) < 700 
     then z t = [] \<and> lOut t = One 
     else z t = [Zero] \<and> lOut t = Zero"
     by (simp add: Controller_L_def)
  show ?thesis
  proof (cases "hd (y t) < 700")
    assume a3:"hd (y t) < 700"
    from a3 and sg1 have "z t = [] \<and> lOut t = One" by simp
    from this and h2 show ?thesis by simp
  next
    assume a4:"\<not> hd (y t) < 700"
    from a4 and sg1 have "z t = [Zero] \<and> lOut t = Zero" by simp
    from this and h3 show ?thesis by simp
  qed
qed

lemma L5_Controller_One:
  assumes h1:"Controller_L y lIn lOut z"
      and h2:"lOut t = One"
      and h3:"z t = []"
  shows "lIn t = One" 
proof (cases "lIn t")
  assume a1:"lIn t = Zero"
  from a1 and h1 have sg1:
    "if 300 < hd (y t) 
     then z t = [] \<and> lOut t = Zero 
     else z t = [One] \<and> lOut t = One"
     by (simp add: Controller_L_def)
  show ?thesis
  proof (cases "300 < hd (y t)")
    assume a3:"300 < hd (y t)"
    from a3 and sg1 have sg2:"z t = [] \<and> lOut t = Zero" by simp
    from this and h2 show ?thesis by simp
  next
    assume a4:"\<not> 300 < hd (y t)"
    from a4 and sg1 have sg3:"z t = [One] \<and> lOut t = One" by simp
    from this and h3 show ?thesis by simp
  qed 
next
  assume "lIn t = One"
  then show ?thesis by simp 
qed

lemma L5_Controller:
  assumes "Controller_L y lIn lOut z"
         and "lOut t = a"
         and "z t = []"
  shows "lIn t = a" 
using assms
by (metis L5_Controller_One L5_Controller_Zero bit.exhaust)

lemma L6_Controller_Zero:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "l (Suc t) = Zero"
         and "z (Suc t) = []"
  shows "l t = Zero"
using assms
by (metis L4_Controller_Zero not_Cons_self2)

lemma L6_Controller_One:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "l (Suc t) = One"
         and "z (Suc t) = []"
  shows "l t = One"
using assms
by (metis L4_Controller_One list.distinct(1))

lemma L6_Controller:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "l (Suc t) = a"
         and "z (Suc t) = []"
  shows "l t = a"
using assms
by (metis L5_Controller correct_fin_inf_append2)

lemma L7_Controller_Zero:
  assumes h1:"Controller_L y (fin_inf_append [Zero] l) l z"
         and h2:"l t = Zero"
  shows      "last (fin_make_untimed (inf_truncate z t)) = Zero"
using assms
proof (induct t)
  case 0  
  from h1 have "z 0 = [Zero]" by (simp add: Controller_L_def) 
  from this show ?case by (simp add: fin_make_untimed_def)
next
   fix t
   case (Suc t)
   from this show ?case
   proof (cases "l t")
     assume a1:"l t = Zero"
     from Suc have
       "(z (Suc t) = [] \<and> l t = Zero) \<or> (z (Suc t) = [Zero] \<and> l t = One)"
       by (simp add: L4_Controller_Zero)
     from this and a1 have "z (Suc t) = []"
       by simp 
     from Suc and this and a1 show ?case
       by (simp add: fin_make_untimed_append_empty)
   next 
     assume a1:"l t = One"
     from Suc have
       "(z (Suc t) = [] \<and> l t = Zero) \<or> (z (Suc t) = [Zero] \<and> l t = One)"
       by (simp add: L4_Controller_Zero)
     from this and a1 have "z (Suc t) = [Zero]"
       by simp 
     from a1 and Suc and this show ?case
       by (simp add: fin_make_untimed_def) 
   qed
qed

lemma L7_Controller_One_l0:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z" 
         and "y 0 = [500::nat]"
  shows    "l 0 = Zero"
proof (rule ccontr)
  assume a1:" \<not> l 0 = Zero" 
  from assms have sg1:"z 0 = [Zero]" by (simp add: Controller_L_def) 
  have sg2:"fin_inf_append [Zero] l (0::nat) = Zero" by  (simp add: fin_inf_append_def)
  from assms and a1 and sg1 and sg2 show "False"
   by (simp add: Controller_L_def) 
qed

lemma L7_Controller_One:
  assumes h1:"Controller_L y (fin_inf_append [Zero] l) l z"
      and h2:"l t = One"
      and h3:"y 0 = [500::nat]"
  shows "last (fin_make_untimed (inf_truncate z t)) = One"
using assms
proof (induct t)
  case 0
  from h1 and h3 have "l 0 = Zero" 
    by (simp add: L7_Controller_One_l0) 
  from this and 0 show ?case by simp
next
   fix t
   case (Suc t)
   from this show ?case
   proof (cases "l t")
     assume a1:"l t = Zero"
     from Suc have
       "(z (Suc t) = [] \<and> l t = One) \<or> (z (Suc t) = [One] \<and> l t = Zero)" 
       by (simp add: L4_Controller_One)
     from this and a1 have "z (Suc t) = [One]"
       by simp  
     from Suc and this and a1 show ?case
       by (simp add: fin_make_untimed_def) 
   next 
     assume a1:"l t = One"
     from Suc have
       "(z (Suc t) = [] \<and> l t = One) \<or> (z (Suc t) = [One] \<and> l t = Zero)" 
       by (simp add: L4_Controller_One)
     from this and a1 have "z (Suc t) = []"
       by simp 
     from a1 and Suc and this show ?case
       by (simp add: fin_make_untimed_def) 
   qed
qed

lemma L7_Controller:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
         and "y 0 = [500::nat]"
  shows      "last (fin_make_untimed (inf_truncate z t)) =  l t"
using assms
by (metis (full_types) L7_Controller_One L7_Controller_Zero bit.exhaust)

lemma L8_Controller:
  assumes "Controller_L y (fin_inf_append [Zero] l) l z"
  shows    "z t = [] \<or> z t = [Zero] \<or> z t = [One]"
proof (cases "fin_inf_append [Zero] l t = Zero")
  assume a1:"fin_inf_append [Zero] l t = Zero"
  from a1 and assms have sg1:
   "if 300 < hd (y t) 
    then z t = [] \<and> l t = Zero 
    else z t = [One] \<and> l t = One"
    by (simp add: Controller_L_def)
  show ?thesis
  proof (cases "300 < hd (y t)")
    assume a11:"300 < hd (y t)"
    from a11 and sg1 show ?thesis by simp
  next
    assume a12:"\<not> 300 < hd (y t)"
    from a12 and sg1 show ?thesis by simp
  qed
next
  assume a2:"fin_inf_append [Zero] l t \<noteq> Zero"
  from a2 and assms have sg2:
   "if hd (y t) < 700 
    then z t = [] \<and> l t = One 
    else z t = [Zero] \<and> l t = Zero"
    by (simp add: Controller_L_def)
  show ?thesis
  proof (cases "hd (y t) < 700")
    assume a21:"hd (y t) < 700"
    from a21 and sg2 show ?thesis by simp
  next
    assume a22:"\<not> hd (y t) < 700"
    from a22 and sg2 show ?thesis by simp
  qed
qed

lemma L9_Controller:
  assumes h1:"Controller_L s (fin_inf_append [Zero] l) l z"
         and h2:"fin_make_untimed (inf_truncate z i) !
              (length (fin_make_untimed (inf_truncate z i)) - Suc 0) =  Zero"
         and h3:"last (fin_make_untimed (inf_truncate z i)) = l i"
         and h5:"hd (s (Suc i)) = hd (s i) - r"
         and h6:"fin_make_untimed (inf_truncate z i) \<noteq> []"
         and h8:"r \<le> 10"
  shows "200 \<le> hd (s (Suc i))"
proof -
  from h6 and h2 and h3 have sg0:"l i = Zero"
    by (simp add: last_nth_length)
  show ?thesis
  proof (cases "fin_inf_append [Zero] l i = Zero")
    assume a1:"fin_inf_append [Zero] l i = Zero"
    from a1 and h1 have sg1:
      "if 300 < hd (s i) 
       then z i = [] \<and> l i = Zero 
       else z i = [One] \<and> l i = One"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "300 < hd (s i)")
      assume a11:"300 < hd (s i)"
      from a11 and h5 and h8 show ?thesis by simp
    next
      assume a12:"\<not> 300 < hd (s i)" 
      from a12 and sg1 and sg0 show ?thesis by simp 
    qed
  next
    assume a2:"fin_inf_append [Zero] l i \<noteq> Zero"
    from a2 and h1 have sg2:
      "if hd (s i) < 700 
       then z i = [] \<and> l i = One 
       else z i = [Zero] \<and> l i = Zero"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "hd (s i) < 700")
      assume a21:"hd (s i) < 700"
      from this and sg2 and sg0 show ?thesis by simp
    next
      assume a22:"\<not> hd (s i) < 700"
      from this and h5 and h8  show ?thesis by simp
    qed
  qed
qed

lemma L10_Controller:
  assumes h1:"Controller_L s (fin_inf_append [Zero] l) l z"
      and h2:"fin_make_untimed (inf_truncate z i) !
              (length (fin_make_untimed (inf_truncate z i)) - Suc 0) \<noteq>  Zero"
      and h3:"last (fin_make_untimed (inf_truncate z i)) = l i"
      and h5:"hd (s (Suc i)) = hd (s i) + r"
      and h6:"fin_make_untimed (inf_truncate z i) \<noteq> []"
      and h8:"r \<le> 10"
  shows "hd (s (Suc i)) \<le> 800"
proof -
  from h6 and h2 and h3 have sg0:"l i \<noteq>  Zero"
    by (simp add: last_nth_length)
  show ?thesis
  proof (cases "fin_inf_append [Zero] l i = Zero")
    assume a1:"fin_inf_append [Zero] l i = Zero"
    from a1 and h1 have sg1:
      "if 300 < hd (s i) 
       then z i = [] \<and> l i = Zero 
       else z i = [One] \<and> l i = One"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "300 < hd (s i)")
      assume a11:"300 < hd (s i)"
      from a11 and sg1 and sg0 show ?thesis by simp
    next
      assume a12:"\<not> 300 < hd (s i)" 
      from h5 and a12 and h8 show ?thesis by simp 
    qed
  next
    assume a2:"fin_inf_append [Zero] l i \<noteq> Zero"
    from a2 and h1 have sg2:
      "if hd (s i) < 700 
       then z i = [] \<and> l i = One 
       else z i = [Zero] \<and> l i = Zero"
       by (simp add: Controller_L_def)
    show ?thesis
    proof (cases "hd (s i) < 700")
      assume a21:"hd (s i) < 700"
      from this and h5 and h8 show ?thesis by simp
    next
      assume a22:"\<not> hd (s i) < 700"
      from this and sg2 and sg0 show ?thesis by simp
    qed
  qed
qed


subsection \<open>Properties of the Converter Component\<close>

lemma L1_Converter:
  assumes "Converter z x"
         and "fin_make_untimed (inf_truncate z t) \<noteq> []"
  shows      "hd (x t) = (fin_make_untimed (inf_truncate z t)) ! 
                 ((length (fin_make_untimed (inf_truncate z t))) - (1::nat))"
using assms
by (simp add: Converter_def)

lemma L1a_Converter:
  assumes "Converter z x"
         and "fin_make_untimed (inf_truncate z t) \<noteq> []"
         and "hd (x t) = Zero"
  shows      "(fin_make_untimed (inf_truncate z t)) ! 
                 ((length (fin_make_untimed (inf_truncate z t))) - (1::nat)) 
              = Zero"
using assms
by (simp add: L1_Converter)
 

subsection \<open>Properties of the System\<close>

lemma L1_ControlSystem:
  assumes "ControlSystemArch s"
  shows "ts s"
proof - 
  from assms obtain x z y 
    where a1:"Converter z x" and a2: "SteamBoiler x s y"
    by (simp only: ControlSystemArch_def, auto)    
  from this have "ts x"
    by (simp add: Converter_def)
  from a2 and this show ?thesis by (rule L1_Boiler) 
qed
 
lemma L2_ControlSystem:
  assumes "ControlSystemArch s"
  shows "(200::nat) \<le> hd (s i)"
proof - 
  from assms obtain x z y 
    where a1:"Converter z x" and a2: "SteamBoiler x s y" and a3:"Controller y z"
    by (simp only: ControlSystemArch_def, auto) 
  from this have sg1:"ts x"  by (simp add: Converter_def)
  from sg1 and a2 have sg2:"ts y"  by (simp add: L2_Boiler)
  from sg1 and a2 have sg3:"y = s" by (simp add: SteamBoiler_def)
  from a1 and a2 and a3 and sg1 and sg2 and sg3 show "200 \<le> hd (s i)"
  proof (induction i)
    case 0
    from this show ?case  by (simp add: L3_Boiler)
  next
    fix i
    case (Suc i)
    from this obtain l
      where a4: "Controller_L s (fin_inf_append [Zero] l) l z"
      by (simp add: Controller_def, atomize, auto)
    from Suc and a4 have sg4:"fin_make_untimed (inf_truncate z i) \<noteq> []"
      by (simp add:  L1_Controller)
    from a2 and sg1 have y0asm:"y 0 = [500::nat]"  by (simp add: SteamBoiler_def)
    from Suc and a4 and sg4 and y0asm have sg5: "last (fin_make_untimed (inf_truncate z i)) =  l i"
      by (simp add: L7_Controller)
    from a2 and sg1 obtain r where
         aa0:"0 < r" and
         aa1:"r \<le> 10" and 
         aa2:"hd (s (Suc i)) = (if hd (x i) = Zero then hd (s i) - r else hd (s i) + r)"
         by (simp add: SteamBoiler_def, auto)
    from Suc and a4 and sg4 and sg5 show ?case
    proof (cases "hd (x i) = Zero")
       assume aaZero:"hd (x i) = Zero"
       from a1 and sg4 and this have
         sg7:"(fin_make_untimed (inf_truncate z i)) ! 
             ((length (fin_make_untimed (inf_truncate z i))) - Suc 0)  = Zero"
         by (simp add: L1_Converter)
       from aa2 and aaZero have sg8:"hd (s (Suc i)) = hd (s i) - r" by simp
       from a4 and sg7 and sg5  and sg8 and sg4 and aa1 show ?thesis
          by (rule L9_Controller)
     next
       assume aaOne:"hd (x i) \<noteq> Zero"
       from a1 and sg4 and this have
         sg7:"(fin_make_untimed (inf_truncate z i)) ! 
             ((length (fin_make_untimed (inf_truncate z i))) - Suc 0) \<noteq> Zero"
         by (simp add: L1_Converter)
       from aa2 and aaOne have sg9:"hd (s (Suc i)) = hd (s i) + r" by simp
       from Suc and this show ?thesis by simp
     qed
  qed
qed 

lemma L3_ControlSystem:
  assumes "ControlSystemArch s"
  shows "hd (s i) \<le> (800:: nat)"
proof - 
  from assms obtain x z y 
    where a1:"Converter z x" and a2: "SteamBoiler x s y" and a3:"Controller y z"
    by (simp only: ControlSystemArch_def, auto) 
  from this have sg1:"ts x"  by (simp add: Converter_def)
  from sg1 and a2 have sg2:"ts y"  by (simp add: L2_Boiler)
  from sg1 and a2 have sg3:"y = s" by (simp add: SteamBoiler_def)
  from a1 and a2 and a3 and sg1 and sg2 and sg3 show "hd (s i) \<le> (800:: nat)"
  proof (induction i)
    case 0
    from this show ?case  by (simp add: L4_Boiler)
  next
    fix i
    case (Suc i)
    from this obtain l
      where a4: "Controller_L s (fin_inf_append [Zero] l) l z"
      by (simp add: Controller_def, atomize, auto)
    from a4 have sg4:"fin_make_untimed (inf_truncate z i) \<noteq> []"
      by (simp add:  L1_Controller)
    from a2 and sg1 have y0asm:"y 0 = [500::nat]"  by (simp add: SteamBoiler_def)
    from Suc and a4 and sg4 and y0asm have sg5: "last (fin_make_untimed (inf_truncate z i)) =  l i"
      by (simp add: L7_Controller)
    from a2 and sg1 obtain r where
         aa0:"0 < r" and
         aa1:"r \<le> 10" and 
         aa2:"hd (s (Suc i)) = (if hd (x i) = Zero then hd (s i) - r else hd (s i) + r)"
         by (simp add: SteamBoiler_def, auto)
    from this and Suc and a4 and sg4 and sg5 show ?case
    proof (cases "hd (x i) = Zero")
       assume aaZero:"hd (x i) = Zero"
       from a1 and sg4 and this have
         sg7:"(fin_make_untimed (inf_truncate z i)) ! 
             ((length (fin_make_untimed (inf_truncate z i))) - Suc 0)  = Zero"
         by (simp add: L1_Converter)
       from aa2 and aaZero have sg8:"hd (s (Suc i)) = hd (s i) - r" by simp
       from this and Suc show ?thesis by simp
     next
       assume aaOne:"hd (x i) \<noteq> Zero"
       from a1 and sg4 and this have
         sg7:"(fin_make_untimed (inf_truncate z i)) ! 
             ((length (fin_make_untimed (inf_truncate z i))) - Suc 0) \<noteq> Zero"
         by (simp add: L1_Converter)
       from aa2 and aaOne have sg9:"hd (s (Suc i)) = hd (s i) + r" by simp
       from a4 and sg7 and sg5 and sg9 and sg4  and aa1 show ?thesis
          by (rule L10_Controller)
     qed
  qed
qed

subsection \<open>Proof of the Refinement Relation\<close>

lemma L0_ControlSystem:
  assumes h1:"ControlSystemArch s"
  shows   "ControlSystem s"
using assms
by (metis ControlSystem_def L1_ControlSystem L2_ControlSystem L3_ControlSystem)
 
end 
