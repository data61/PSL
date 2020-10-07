(* Title: thys/Rec_Def.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

theory Rec_Def
  imports Main
begin

datatype recf =  z
  |  s
  |  id nat nat
  |  Cn nat recf "recf list"
  |  Pr nat recf recf
  |  Mn nat recf 

definition pred_of_nl :: "nat list \<Rightarrow> nat list"
  where
    "pred_of_nl xs = butlast xs @ [last xs - 1]"

function rec_exec :: "recf \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "rec_exec z xs = 0" |
    "rec_exec s xs = (Suc (xs ! 0))" |
    "rec_exec (id m n) xs = (xs ! n)" |
    "rec_exec (Cn n f gs) xs = 
     rec_exec f (map (\<lambda> a. rec_exec a xs) gs)" | 
    "rec_exec (Pr n f g) xs = 
     (if last xs = 0 then rec_exec f (butlast xs)
      else rec_exec g (butlast xs @ (last xs - 1) # [rec_exec (Pr n f g) (butlast xs @ [last xs - 1])]))" |
    "rec_exec (Mn n f) xs = (LEAST x. rec_exec f (xs @ [x]) = 0)"
  by pat_completeness auto

termination
  apply(relation "measures [\<lambda> (r, xs). size r, (\<lambda> (r, xs). last xs)]")
        apply(auto simp add: less_Suc_eq_le intro: trans_le_add2 size_list_estimation'[THEN trans_le_add1])
  done

inductive terminate :: "recf \<Rightarrow> nat list \<Rightarrow> bool"
  where
    termi_z: "terminate z [n]"
  | termi_s: "terminate s [n]"
  | termi_id: "\<lbrakk>n < m; length xs = m\<rbrakk> \<Longrightarrow> terminate (id m n) xs"
  | termi_cn: "\<lbrakk>terminate f (map (\<lambda>g. rec_exec g xs) gs); 
              \<forall>g \<in> set gs. terminate g xs; length xs = n\<rbrakk> \<Longrightarrow> terminate (Cn n f gs) xs"
  | termi_pr: "\<lbrakk>\<forall> y < x. terminate g (xs @ y # [rec_exec (Pr n f g) (xs @ [y])]);
              terminate f xs;
              length xs = n\<rbrakk> 
              \<Longrightarrow> terminate (Pr n f g) (xs @ [x])"
  | termi_mn: "\<lbrakk>length xs = n; terminate f (xs @ [r]); 
              rec_exec f (xs @ [r]) = 0;
              \<forall> i < r. terminate f (xs @ [i]) \<and> rec_exec f (xs @ [i]) > 0\<rbrakk> \<Longrightarrow> terminate (Mn n f) xs"


end