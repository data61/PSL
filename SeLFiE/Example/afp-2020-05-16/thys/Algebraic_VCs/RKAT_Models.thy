(* Title: Models of Refinement KAT
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection \<open>Models of Refinement KAT\<close>

theory RKAT_Models
  imports RKAT
   
begin

text \<open>So far only the relational model is developed.\<close>

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.H P X Q}"

interpretation rel_rkat: rkat "(\<union>)" "(;)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.H_def)

end



