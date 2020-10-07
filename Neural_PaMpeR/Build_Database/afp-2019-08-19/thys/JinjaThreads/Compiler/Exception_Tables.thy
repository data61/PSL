(*  Title:      JinjaThreads/Compiler/Exception_Tables.thy
    Author:     Andreas Lochbihler
*)

section \<open>Various Operations for Exception Tables\<close>

theory Exception_Tables imports
  Compiler2
  "../Common/ExternalCallWF"
  "../JVM/JVMExceptions"
begin

definition pcs :: "ex_table \<Rightarrow> nat set"
where "pcs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {f ..< t}"

lemma pcs_subset:
  fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows "pcs(compxE2 e pc d) \<subseteq> {pc..<pc+size(compE2 e)}"
  and "pcs(compxEs2 es pc d) \<subseteq> {pc..<pc+size(compEs2 es)}" 
apply(induct e pc d and es pc d rule: compxE2_compxEs2_induct)
apply (simp_all add:pcs_def)
apply (fastforce)+
done

lemma pcs_Nil [simp]: "pcs [] = {}"
by(simp add:pcs_def)

lemma pcs_Cons [simp]: "pcs (x#xt) = {fst x ..< fst(snd x)} \<union> pcs xt"
by(auto simp add: pcs_def)

lemma pcs_append [simp]: "pcs(xt\<^sub>1 @ xt\<^sub>2) = pcs xt\<^sub>1 \<union> pcs xt\<^sub>2"
by(simp add:pcs_def)

lemma [simp]: "pc < pc\<^sub>0 \<or> pc\<^sub>0+size(compE2 e) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxE2 e pc\<^sub>0 d)"
using pcs_subset by fastforce

lemma [simp]: "pc < pc0 \<or> pc0+size(compEs2 es) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxEs2 es pc0 d)"
using pcs_subset by fastforce

lemma [simp]: "pc1 + size(compE2 e1) \<le> pc2 \<Longrightarrow> pcs(compxE2 e1 pc1 d1) \<inter> pcs(compxE2 e2 pc2 d2) = {}"
using pcs_subset by fastforce

lemma [simp]: "pc\<^sub>1 + size(compE2 e) \<le> pc\<^sub>2 \<Longrightarrow> pcs(compxE2 e pc\<^sub>1 d\<^sub>1) \<inter> pcs(compxEs2 es pc\<^sub>2 d\<^sub>2) = {}"
using pcs_subset by fastforce

lemma match_ex_table_append_not_pcs [simp]:
 "pc \<notin> pcs xt0 \<Longrightarrow> match_ex_table P C pc (xt0 @ xt1) = match_ex_table P C pc xt1"
by (induct xt0) (auto simp: matches_ex_entry_def)

lemma outside_pcs_not_matches_entry [simp]:
  "\<lbrakk> x \<in> set xt; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> \<not> matches_ex_entry P D pc x"
by(auto simp:matches_ex_entry_def pcs_def)

lemma outside_pcs_compxE2_not_matches_entry [simp]:
  assumes xe: "xe \<in> set(compxE2 e pc d)"
  and outside: "pc' < pc \<or> pc+size(compE2 e) \<le> pc'"
  shows "\<not> matches_ex_entry P C pc' xe"
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxE2 e pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed

lemma outside_pcs_compxEs2_not_matches_entry [simp]:
  assumes xe: "xe \<in> set(compxEs2 es pc d)" 
  and outside: "pc' < pc \<or> pc+size(compEs2 es) \<le> pc'"
  shows "\<not> matches_ex_entry P C pc' xe"
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxEs2 es pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed

lemma match_ex_table_app[simp]:
  "\<forall>xte \<in> set xt\<^sub>1. \<not> matches_ex_entry P D pc xte \<Longrightarrow>
  match_ex_table P D pc (xt\<^sub>1 @ xt) = match_ex_table P D pc xt"
by(induct xt\<^sub>1) simp_all

lemma match_ex_table_eq_NoneI [simp]:
  "\<forall>x \<in> set xtab. \<not> matches_ex_entry P C pc x \<Longrightarrow>
  match_ex_table P C pc xtab = None"
using match_ex_table_app[where ?xt = "[]"] by fastforce

lemma match_ex_table_not_pcs_None:
  "pc \<notin> pcs xt \<Longrightarrow> match_ex_table P C pc xt = None"
by(auto intro: match_ex_table_eq_NoneI)

lemma match_ex_entry:
  fixes start shows
  "matches_ex_entry P C pc (start, end, catch_type, handler) =
  (start \<le> pc \<and> pc < end \<and> (case catch_type of None \<Rightarrow> True | \<lfloor>C'\<rfloor> \<Rightarrow> P \<turnstile> C \<preceq>\<^sup>* C'))"
by(simp add:matches_ex_entry_def)

lemma pcs_compxE2D [dest]:
  "pc \<in> pcs (compxE2 e pc' d) \<Longrightarrow> pc' \<le> pc \<and> pc < pc' + length (compE2 e)"
using pcs_subset by(fastforce)

lemma pcs_compxEs2D [dest]:
  "pc \<in> pcs (compxEs2 es pc' d) \<Longrightarrow> pc' \<le> pc \<and> pc < pc' + length (compEs2 es)"
using pcs_subset by(fastforce)

definition shift :: "nat \<Rightarrow> ex_table \<Rightarrow> ex_table"
where
  "shift n xt \<equiv> map (\<lambda>(from,to,C,handler,depth). (n+from,n+to,C,n+handler,depth)) xt"

lemma shift_0 [simp]: "shift 0 xt = xt"
by(induct xt)(auto simp:shift_def)

lemma shift_Nil [simp]: "shift n [] = []"
by(simp add:shift_def)

lemma shift_Cons_tuple [simp]:
  "shift n ((from, to, C, handler, depth) # xt) = (from + n, to + n, C, handler + n, depth) # shift n xt"
by(simp add: shift_def)

lemma shift_append [simp]: "shift n (xt\<^sub>1 @ xt\<^sub>2) = shift n xt\<^sub>1 @ shift n xt\<^sub>2"
by(simp add:shift_def)

lemma shift_shift [simp]: "shift m (shift n xt) = shift (m+n) xt"
by(simp add: shift_def split_def)

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows shift_compxE2: "shift pc (compxE2 e pc' d) = compxE2 e (pc' + pc) d"
  and  shift_compxEs2: "shift pc (compxEs2 es pc' d) = compxEs2 es (pc' + pc) d"
by(induct e and es arbitrary: pc pc' d and pc pc' d rule: compE2.induct compEs2.induct)
  (auto simp:shift_def ac_simps)

lemma compxE2_size_convs [simp]: "n \<noteq> 0 \<Longrightarrow> compxE2 e n d = shift n (compxE2 e 0 d)"
 and compxEs2_size_convs: "n \<noteq> 0 \<Longrightarrow> compxEs2 es n d = shift n (compxEs2 es 0 d)" 
by(simp_all add:shift_compxE2 shift_compxEs2)

lemma pcs_shift_conv [simp]: "pcs (shift n xt) = (+) n ` pcs xt"
apply(auto simp add: shift_def pcs_def)
apply(rule_tac x="x-n" in image_eqI)
apply(auto)
apply(rule bexI)
 prefer 2
 apply(assumption)
apply(auto)
done

lemma image_plus_const_conv [simp]:
  fixes m :: nat
  shows "m \<in> (+) n ` A \<longleftrightarrow> m \<ge> n \<and> m - n \<in> A"
by(force)

lemma match_ex_table_shift_eq_None_conv [simp]:
  "match_ex_table P C pc (shift n xt) = None \<longleftrightarrow> pc < n \<or> match_ex_table P C (pc - n) xt = None"
by(induct xt)(auto simp add: match_ex_entry split: if_split_asm)

lemma match_ex_table_shift_pc_None:
  "pc \<ge> n \<Longrightarrow> match_ex_table P C pc (shift n xt) = None \<longleftrightarrow> match_ex_table P C (pc - n) xt = None"
by(simp add: match_ex_table_shift_eq_None_conv)

lemma match_ex_table_shift_eq_Some_conv [simp]:
  "match_ex_table P C pc (shift n xt) = \<lfloor>(pc', d)\<rfloor> \<longleftrightarrow>
   pc \<ge> n \<and> pc' \<ge> n \<and> match_ex_table P C (pc - n) xt = \<lfloor>(pc' - n, d)\<rfloor>"
by(induct xt)(auto simp add: match_ex_entry split: if_split_asm)

lemma match_ex_table_shift:
 "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C (n + pc) (shift n xt) = \<lfloor>(n + pc', d)\<rfloor>"
by(simp add: match_ex_table_shift_eq_Some_conv)

lemma match_ex_table_shift_pcD:
  "match_ex_table P C pc (shift n xt) = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> pc \<ge> n \<and> pc' \<ge> n \<and> match_ex_table P C (pc - n) xt = \<lfloor>(pc' - n, d)\<rfloor>"
by(simp add: match_ex_table_shift_eq_Some_conv)

lemma match_ex_table_pcsD: "match_ex_table P C pc xt = \<lfloor>(pc', D)\<rfloor> \<Longrightarrow> pc \<in> pcs xt"
by(induct xt)(auto split: if_split_asm simp add: match_ex_entry)


definition stack_xlift :: "nat \<Rightarrow> ex_table \<Rightarrow> ex_table"
where "stack_xlift n xt \<equiv> map (\<lambda>(from,to,C,handler,depth). (from, to, C, handler, n + depth)) xt"

lemma stack_xlift_0 [simp]: "stack_xlift 0 xt = xt"
by(induct xt, auto simp add: stack_xlift_def)

lemma stack_xlift_Nil [simp]: "stack_xlift n [] = []"
by(simp add: stack_xlift_def)

lemma stack_xlift_Cons_tuple [simp]:
  "stack_xlift n ((from, to, C, handler, depth) # xt) = (from, to, C, handler, depth + n) # stack_xlift n xt"
by(simp add: stack_xlift_def)

lemma stack_xlift_append [simp]: "stack_xlift n (xt @ xt') = stack_xlift n xt @ stack_xlift n xt'"
by(simp add: stack_xlift_def)

lemma stack_xlift_stack_xlift [simp]: "stack_xlift n (stack_xlift m xt) = stack_xlift (n + m) xt"
by(simp add: stack_xlift_def split_def)

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows stack_xlift_compxE2: "stack_xlift n (compxE2 e pc d) = compxE2 e pc (n + d)"
  and stack_xlift_compxEs2: "stack_xlift n (compxEs2 es pc d) = compxEs2 es pc (n + d)"
by(induct e and es arbitrary: d pc and d pc rule: compE2.induct compEs2.induct)
  (auto simp add: shift_compxE2 simp del: compxE2_size_convs)

lemma compxE2_stack_xlift_convs [simp]: "d > 0 \<Longrightarrow> compxE2 e pc d = stack_xlift d (compxE2 e pc 0)"
  and compxEs2_stack_xlift_convs [simp]: "d > 0 \<Longrightarrow> compxEs2 es pc d = stack_xlift d (compxEs2 es pc 0)"
by(simp_all add: stack_xlift_compxE2 stack_xlift_compxEs2)

lemma stack_xlift_shift [simp]: "stack_xlift d (shift n xt) = shift n (stack_xlift d xt)"
by(induct xt)(auto)

lemma pcs_stack_xlift_conv [simp]: "pcs (stack_xlift n xt) = pcs xt"
by(auto simp add: pcs_def stack_xlift_def)

lemma match_ex_table_stack_xlift_eq_None_conv [simp]:
  "match_ex_table P C pc (stack_xlift d xt) = None \<longleftrightarrow> match_ex_table P C pc xt = None"
by(induct xt)(auto simp add: match_ex_entry)

lemma match_ex_table_stack_xlift_eq_Some_conv [simp]:
  "match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', d)\<rfloor> \<longleftrightarrow> d \<ge> n \<and> match_ex_table P C pc xt = \<lfloor>(pc', d - n)\<rfloor>"
by(induct xt)(auto simp add: match_ex_entry)

lemma match_ex_table_stack_xliftD:
  "match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> d \<ge> n \<and> match_ex_table P C pc xt = \<lfloor>(pc', d - n)\<rfloor>"
by(simp)

lemma match_ex_table_stack_xlift:
  "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C pc (stack_xlift n xt) = \<lfloor>(pc', n + d)\<rfloor>"
by simp

lemma pcs_stack_xlift: "pcs (stack_xlift n xt) = pcs xt"
by(auto simp add: stack_xlift_def pcs_def)

lemma match_ex_table_None_append [simp]:
  "match_ex_table P C pc xt = None
  \<Longrightarrow> match_ex_table P C pc (xt @ xt') = match_ex_table P C pc xt'"
by(induct xt, auto)

lemma match_ex_table_Some_append [simp]: 
  "match_ex_table P C pc xt = \<lfloor>(pc', d)\<rfloor> \<Longrightarrow> match_ex_table P C pc (xt @ xt') = \<lfloor>(pc', d)\<rfloor>"
by(induct xt)(auto)

lemma match_ex_table_append:
  "match_ex_table P C pc (xt @ xt') = (case match_ex_table P C pc xt of None \<Rightarrow> match_ex_table P C pc xt' 
                                                                  | Some pcd \<Rightarrow> Some pcd)"
by(auto)

lemma match_ex_table_pc_length_compE2:
  "match_ex_table P a pc (compxE2 e pc' d) = \<lfloor>pcd\<rfloor> \<Longrightarrow> pc' \<le> pc \<and> pc < length (compE2 e) + pc'"
  
  and match_ex_table_pc_length_compEs2:
  "match_ex_table P a pc (compxEs2 es pc' d) = \<lfloor>pcd\<rfloor> \<Longrightarrow> pc' \<le> pc \<and> pc < length (compEs2 es) + pc'"
using pcs_subset by(cases pcd, fastforce dest!: match_ex_table_pcsD)+

lemma match_ex_table_compxE2_shift_conv:
  "f > 0 \<Longrightarrow> match_ex_table P C pc (compxE2 e f d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> pc \<ge> f \<and> pc' \<ge> f \<and> match_ex_table P C (pc - f) (compxE2 e 0 d) = \<lfloor>(pc' - f, d')\<rfloor>"
by simp

lemma match_ex_table_compxEs2_shift_conv:
  "f > 0 \<Longrightarrow> match_ex_table P C pc (compxEs2 es f d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> pc \<ge> f \<and> pc' \<ge> f \<and> match_ex_table P C (pc - f) (compxEs2 es 0 d) = \<lfloor>(pc' - f, d')\<rfloor>"
by(simp add: compxEs2_size_convs)

lemma match_ex_table_compxE2_stack_conv:
  "d > 0 \<Longrightarrow> match_ex_table P C pc (compxE2 e 0 d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> d' \<ge> d \<and> match_ex_table P C pc (compxE2 e 0 0) = \<lfloor>(pc', d' - d)\<rfloor>"
by simp

lemma match_ex_table_compxEs2_stack_conv:
  "d > 0 \<Longrightarrow> match_ex_table P C pc (compxEs2 es 0 d) = \<lfloor>(pc', d')\<rfloor> \<longleftrightarrow> d' \<ge> d \<and> match_ex_table P C pc (compxEs2 es 0 0) = \<lfloor>(pc', d' - d)\<rfloor>"
by(simp add: compxEs2_stack_xlift_convs)

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows match_ex_table_compxE2_not_same: "match_ex_table P C pc (compxE2 e n d) = \<lfloor>(pc', d')\<rfloor> \<Longrightarrow> pc \<noteq> pc'"
  and match_ex_table_compxEs2_not_same:"match_ex_table P C pc (compxEs2 es n d) = \<lfloor>(pc', d')\<rfloor> \<Longrightarrow> pc \<noteq> pc'"
apply(induct e n d and es n d rule: compxE2_compxEs2_induct)
apply(auto simp add: match_ex_table_append match_ex_entry simp del: compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs split: if_split_asm)
done

end
