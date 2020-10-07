(*<*)
(*
   Title:  Theory SteamBoiler.thy (Steam Boiler System: Specification)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

section \<open>Steam Boiler System: Specification\<close>

theory  SteamBoiler 
imports stream BitBoolTS
begin

definition
 ControlSystem :: "nat istream \<Rightarrow> bool"
where
 "ControlSystem s \<equiv>  
  (ts s) \<and> 
   (\<forall> (j::nat). (200::nat) \<le> hd (s j) \<and> hd (s j) \<le> (800:: nat))"

definition
  SteamBoiler :: "bit istream \<Rightarrow> nat istream \<Rightarrow> nat istream \<Rightarrow> bool"
where
 "SteamBoiler x s y \<equiv>  
  ts x 
  \<longrightarrow> 
  ((ts y) \<and> (ts s) \<and> (y = s) \<and> 
   ((s 0) = [500::nat]) \<and> 
   (\<forall> (j::nat). (\<exists> (r::nat). 
                (0::nat) < r \<and> r \<le> (10::nat) \<and> 
                hd (s (Suc j)) = 
                   (if hd (x j) = Zero 
                    then (hd (s j)) - r 
                    else (hd (s j)) + r)) ))"

definition
  Converter :: "bit istream \<Rightarrow> bit istream \<Rightarrow> bool"
where
 "Converter z x 
  \<equiv> 
  (ts x) 
  \<and> 
  (\<forall> (t::nat). 
    hd (x t) = 
        (if  (fin_make_untimed (inf_truncate z t) = [])
         then  
             Zero
         else 
             (fin_make_untimed (inf_truncate z t)) ! 
                 ((length (fin_make_untimed (inf_truncate z t))) - (1::nat)) 
       ))"

definition
  Controller_L :: 
    "nat istream \<Rightarrow> bit iustream \<Rightarrow> bit iustream \<Rightarrow> bit istream \<Rightarrow> bool"
where
 "Controller_L y lIn lOut z 
  \<equiv> 
  (z 0 = [Zero]) 
  \<and>
  (\<forall> (t::nat). 
  ( if (lIn t) = Zero 
    then ( if 300 < hd (y t)  
           then  (z t) = []    \<and> (lOut t) = Zero
           else  (z t) = [One] \<and> (lOut t) = One 
          )
    else ( if  hd (y t) < 700  
           then  (z t) = []     \<and> (lOut t) = One   
           else  (z t) = [Zero] \<and> (lOut t) = Zero ) ))"

definition 
  Controller :: "nat istream \<Rightarrow> bit istream \<Rightarrow> bool"
where
 "Controller y z 
  \<equiv> 
  (ts y)
  \<longrightarrow> 
  (\<exists> l. Controller_L y (fin_inf_append [Zero] l) l z)"

definition
  ControlSystemArch :: "nat istream \<Rightarrow> bool"
where
 "ControlSystemArch s 
  \<equiv> 
  \<exists> x z :: bit istream. \<exists> y :: nat istream.
    ( SteamBoiler x s y \<and> Controller y z \<and> Converter z x )"

end 
