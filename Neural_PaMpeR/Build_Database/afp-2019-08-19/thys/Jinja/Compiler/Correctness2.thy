(*  Title:      Jinja/Compiler/Correctness2.thy
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

section \<open>Correctness of Stage 2\<close>

theory Correctness2
imports "HOL-Library.Sublist" Compiler2
begin

(*<*)hide_const (open) Throw(*>*)

subsection\<open>Instruction sequences\<close>

text\<open>How to select individual instructions and subsequences of
instructions from a program given the class, method and program
counter.\<close>

definition before :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr list \<Rightarrow> bool"
   ("(_,_,_,_/ \<rhd> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<rhd> is \<longleftrightarrow> prefix is (drop pc (instrs_of P C M))"

definition at :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr \<Rightarrow> bool"
   ("(_,_,_,_/ \<triangleright> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<triangleright> i \<longleftrightarrow> (\<exists>is. drop pc (instrs_of P C M) = i#is)"

lemma [simp]: "P,C,M,pc \<rhd> []"
(*<*)by(simp add:before_def)(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (i#is) = (P,C,M,pc \<triangleright> i \<and> P,C,M,pc + 1 \<rhd> is)"
(*<*)by(fastforce simp add:before_def at_def prefix_def drop_Suc drop_tl)(*>*)

(*<*)
declare drop_drop[simp del]
(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (is\<^sub>1 @ is\<^sub>2) = (P,C,M,pc \<rhd> is\<^sub>1 \<and> P,C,M,pc + size is\<^sub>1 \<rhd> is\<^sub>2)"
(*<*)
apply(simp add:before_def prefix_def)
apply(subst add.commute)
apply(simp add: drop_drop[symmetric])
apply fastforce
done
(*>*)

(*<*)
declare drop_drop[simp]
(*>*)


lemma [simp]: "P,C,M,pc \<triangleright> i \<Longrightarrow> instrs_of P C M ! pc = i"
(*<*)by(clarsimp simp add:at_def strict_prefix_def nth_via_drop)(*>*)


lemma beforeM:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D \<Longrightarrow>
  compP\<^sub>2 P,D,M,0 \<rhd> compE\<^sub>2 body @ [Return]"
(*<*)
apply(drule sees_method_idemp)
apply(simp add:before_def compP\<^sub>2_def compMb\<^sub>2_def)
done
(*>*)

text\<open>This lemma executes a single instruction by rewriting:\<close>

lemma [simp]:
  "P,C,M,pc \<triangleright> instr \<Longrightarrow>
  (P \<turnstile> (None, h, (vs,ls,C,M,pc) # frs) -jvm\<rightarrow> \<sigma>') =
  ((None, h, (vs,ls,C,M,pc) # frs) = \<sigma>' \<or>
   (\<exists>\<sigma>. exec(P,(None, h, (vs,ls,C,M,pc) # frs)) = Some \<sigma> \<and> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'))"
(*<*)
apply(simp only: exec_all_def)
apply(blast intro: converse_rtranclE converse_rtrancl_into_rtrancl)
done
(*>*)


subsection\<open>Exception tables\<close>

definition pcs :: "ex_table \<Rightarrow> nat set"
where
  "pcs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {f ..< t}"

lemma pcs_subset:
shows "\<And>pc d. pcs(compxE\<^sub>2 e pc d) \<subseteq> {pc..<pc+size(compE\<^sub>2 e)}"
and "\<And>pc d. pcs(compxEs\<^sub>2 es pc d) \<subseteq> {pc..<pc+size(compEs\<^sub>2 es)}"
(*<*)
apply(induct e and es rule: compxE\<^sub>2.induct compxEs\<^sub>2.induct)
apply (simp_all add:pcs_def)
apply (fastforce split:bop.splits)+
done
(*>*)


lemma [simp]: "pcs [] = {}"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pcs (x#xt) = {fst x ..< fst(snd x)} \<union> pcs xt"
(*<*)by(auto simp add: pcs_def)(*>*)


lemma [simp]: "pcs(xt\<^sub>1 @ xt\<^sub>2) = pcs xt\<^sub>1 \<union> pcs xt\<^sub>2"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pc < pc\<^sub>0 \<or> pc\<^sub>0+size(compE\<^sub>2 e) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxE\<^sub>2 e pc\<^sub>0 d)"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc < pc\<^sub>0 \<or> pc\<^sub>0+size(compEs\<^sub>2 es) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxEs\<^sub>2 es pc\<^sub>0 d)"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc\<^sub>1 + size(compE\<^sub>2 e\<^sub>1) \<le> pc\<^sub>2 \<Longrightarrow> pcs(compxE\<^sub>2 e\<^sub>1 pc\<^sub>1 d\<^sub>1) \<inter> pcs(compxE\<^sub>2 e\<^sub>2 pc\<^sub>2 d\<^sub>2) = {}"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc\<^sub>1 + size(compE\<^sub>2 e) \<le> pc\<^sub>2 \<Longrightarrow> pcs(compxE\<^sub>2 e pc\<^sub>1 d\<^sub>1) \<inter> pcs(compxEs\<^sub>2 es pc\<^sub>2 d\<^sub>2) = {}"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]:
 "pc \<notin> pcs xt\<^sub>0 \<Longrightarrow> match_ex_table P C pc (xt\<^sub>0 @ xt\<^sub>1) = match_ex_table P C pc xt\<^sub>1"
(*<*)by (induct xt\<^sub>0) (auto simp: matches_ex_entry_def)(*>*)


lemma [simp]: "\<lbrakk> x \<in> set xt; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> \<not> matches_ex_entry P D pc x"
(*<*)by(auto simp:matches_ex_entry_def pcs_def)(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxE\<^sub>2 e pc d)" and outside: "pc' < pc \<or> pc+size(compE\<^sub>2 e) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxE\<^sub>2 e pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxEs\<^sub>2 es pc d)" and outside: "pc' < pc \<or> pc+size(compEs\<^sub>2 es) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxEs\<^sub>2 es pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma match_ex_table_app[simp]:
  "\<forall>xte \<in> set xt\<^sub>1. \<not> matches_ex_entry P D pc xte \<Longrightarrow>
  match_ex_table P D pc (xt\<^sub>1 @ xt) = match_ex_table P D pc xt"
(*<*)by(induct xt\<^sub>1) simp_all(*>*)


lemma [simp]:
  "\<forall>x \<in> set xtab. \<not> matches_ex_entry P C pc x \<Longrightarrow>
  match_ex_table P C pc xtab = None"
(*<*)using match_ex_table_app[where ?xt = "[]"] by fastforce(*>*)


lemma match_ex_entry:
  "matches_ex_entry P C pc (start, end, catch_type, handler) =
  (start \<le> pc \<and> pc < end \<and>  P \<turnstile> C \<preceq>\<^sup>* catch_type)"
(*<*)by(simp add:matches_ex_entry_def)(*>*)


definition caught :: "jvm_prog \<Rightarrow> pc \<Rightarrow> heap \<Rightarrow> addr \<Rightarrow> ex_table \<Rightarrow> bool" where
  "caught P pc h a xt \<longleftrightarrow>
  (\<exists>entry \<in> set xt. matches_ex_entry P (cname_of h a) pc entry)"

definition beforex :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"
              ("(2_,/_,/_ \<rhd>/ _ /'/ _,/_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<rhd> xt / I,d \<longleftrightarrow>
  (\<exists>xt\<^sub>0 xt\<^sub>1. ex_table_of P C M = xt\<^sub>0 @ xt @ xt\<^sub>1 \<and> pcs xt\<^sub>0 \<inter> I = {} \<and> pcs xt \<subseteq> I \<and>
    (\<forall>pc \<in> I. \<forall>C pc' d'. match_ex_table P C pc xt\<^sub>1 = \<lfloor>(pc',d')\<rfloor> \<longrightarrow> d' \<le> d))"

definition dummyx :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"  ("(2_,_,_ \<triangleright>/ _ '/_,_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<triangleright> xt/I,d \<longleftrightarrow> P,C,M \<rhd> xt/I,d"

lemma beforexD1: "P,C,M \<rhd> xt / I,d \<Longrightarrow> pcs xt \<subseteq> I"
(*<*)by(auto simp add:beforex_def)(*>*)


lemma beforex_mono: "\<lbrakk> P,C,M \<rhd> xt/I,d'; d' \<le> d \<rbrakk> \<Longrightarrow> P,C,M \<rhd> xt/I,d"
(*<*)by(fastforce simp:beforex_def)(*>*)


lemma [simp]: "P,C,M \<rhd> xt/I,d \<Longrightarrow> P,C,M \<rhd> xt/I,Suc d"
(*<*)by(fastforce intro:beforex_mono)(*>*)


lemma beforex_append[simp]:
  "pcs xt\<^sub>1 \<inter> pcs xt\<^sub>2 = {} \<Longrightarrow>
  P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2/I,d =
  (P,C,M \<rhd> xt\<^sub>1/I-pcs xt\<^sub>2,d  \<and>  P,C,M \<rhd> xt\<^sub>2/I-pcs xt\<^sub>1,d \<and> P,C,M \<triangleright> xt\<^sub>1@xt\<^sub>2/I,d)"
(*<*)
apply(rule iffI)
 prefer 2
 apply(simp add:dummyx_def)
apply(auto simp add: beforex_def dummyx_def)
 apply(rule_tac x = xt\<^sub>0 in exI)
 apply auto
apply(rule_tac x = "xt\<^sub>0@xt\<^sub>1" in exI)
apply auto
done
(*>*)


lemma beforex_appendD1:
  "\<lbrakk> P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^sub>1 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^sub>2 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^sub>1 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule exI,rule exI,rule conjI, rule refl)
apply(rule conjI, blast)
apply(auto)
apply(subgoal_tac "pc \<notin> pcs xt\<^sub>2")
 prefer 2 apply blast
apply (auto split:if_split_asm)
done
(*>*)


lemma beforex_appendD2:
  "\<lbrakk> P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^sub>2 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^sub>1 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^sub>2 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule_tac x = "xt\<^sub>0 @ xt\<^sub>1" in exI)
apply fastforce
done
(*>*)


lemma beforexM:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D \<Longrightarrow>
  compP\<^sub>2 P,D,M \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
(*<*)
apply(drule sees_method_idemp)
apply(drule sees_method_compP[where f = compMb\<^sub>2])
apply(simp add:beforex_def compP\<^sub>2_def compMb\<^sub>2_def)
apply(rule_tac x = "[]" in exI)
using pcs_subset apply fastforce
done
(*>*)


lemma match_ex_table_SomeD2:
 "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
    P,C,M \<rhd> xt/I,d; \<forall>x \<in> set xt. \<not> matches_ex_entry P D pc x; pc \<in> I \<rbrakk>
 \<Longrightarrow> d' \<le> d"
(*<*)
apply(auto simp:beforex_def)
apply(subgoal_tac "pc \<notin> pcs xt\<^sub>0")
apply auto
done
(*>*)


lemma match_ex_table_SomeD1:
  "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
     P,C,M \<rhd> xt / I,d; pc \<in> I; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> d' \<le> d"
(*<*)by(auto elim: match_ex_table_SomeD2)(*>*)


subsection\<open>The correctness proof\<close>

(*<*)
declare nat_add_distrib[simp] caught_def[simp]
declare fun_upd_apply[simp del]
(*>*)


definition
  handle :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> frame list
                \<Rightarrow> jvm_state" where
  "handle P C M a h vs ls pc frs = find_handler P a h ((vs,ls,C,M,pc) # frs)"

lemma handle_Cons:
 "\<lbrakk> P,C,M \<rhd> xt/I,d; d \<le> size vs; pc \<in> I;
    \<forall>x \<in> set xt. \<not> matches_ex_entry P (cname_of h xa) pc x \<rbrakk> \<Longrightarrow>
  handle P C M xa h (v # vs) ls pc frs = handle P C M xa h vs ls pc frs"
(*<*)by(auto simp:handle_def Suc_diff_le dest: match_ex_table_SomeD2)(*>*)

lemma handle_append:
 "\<lbrakk> P,C,M \<rhd> xt/I,d; d \<le> size vs; pc \<in> I; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow>
  handle P C M xa h (ws @ vs) ls pc frs = handle P C M xa h vs ls pc frs"
(*<*)
apply(auto simp:handle_def)
apply(rename_tac pc' d')
apply(subgoal_tac "size ws \<le> length ws + length vs - d'")
apply(simp add:drop_all)
apply(fastforce dest:match_ex_table_SomeD2 split:nat_diff_split)
done
(*>*)


lemma aux_isin[simp]: "\<lbrakk> B \<subseteq> A; a \<in> B \<rbrakk> \<Longrightarrow> a \<in> A"
(*<*)by blast(*>*)


lemma fixes P\<^sub>1 defines [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
shows Jcc:
  "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>e,(h\<^sub>0,ls\<^sub>0)\<rangle> \<Rightarrow> \<langle>ef,(h\<^sub>1,ls\<^sub>1)\<rangle> \<Longrightarrow>
  (\<And>C M pc v xa vs frs I.
     \<lbrakk> P,C,M,pc \<rhd> compE\<^sub>2 e; P,C,M \<rhd> compxE\<^sub>2 e pc (size vs)/I,size vs;
       {pc..<pc+size(compE\<^sub>2 e)} \<subseteq> I \<rbrakk> \<Longrightarrow>
     (ef = Val v \<longrightarrow>
      P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 e))#frs))
     \<and>
     (ef = Throw xa \<longrightarrow>
      (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h\<^sub>1 xa (compxE\<^sub>2 e pc (size vs)) \<and>
               P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow> handle P C M xa h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs)))"
(*<*)
  (is "_ \<Longrightarrow> (\<And>C M pc v xa vs frs I.
                  PROP ?P e h\<^sub>0 ls\<^sub>0 ef h\<^sub>1 ls\<^sub>1 C M pc v xa vs frs I)")
(*>*)

and "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>0,ls\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>fs,(h\<^sub>1,ls\<^sub>1)\<rangle> \<Longrightarrow>
    (\<And>C M pc ws xa es' vs frs I.
      \<lbrakk> P,C,M,pc \<rhd> compEs\<^sub>2 es; P,C,M \<rhd> compxEs\<^sub>2 es pc (size vs)/I,size vs;
       {pc..<pc+size(compEs\<^sub>2 es)} \<subseteq> I \<rbrakk> \<Longrightarrow>
      (fs = map Val ws \<longrightarrow>
       P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(rev ws @ vs,ls\<^sub>1,C,M,pc+size(compEs\<^sub>2 es))#frs))
      \<and>
      (fs = map Val ws @ Throw xa # es' \<longrightarrow>
       (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compEs\<^sub>2 es) \<and>
                \<not> caught P pc\<^sub>1 h\<^sub>1 xa (compxEs\<^sub>2 es pc (size vs)) \<and>
                P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow> handle P C M xa h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs)))"
(*<*)
  (is "_ \<Longrightarrow> (\<And>C M pc ws xa es' vs frs I.
                  PROP ?Ps es h\<^sub>0 ls\<^sub>0 fs h\<^sub>1 ls\<^sub>1 C M pc ws xa es' vs frs I)")
proof (induct rule:eval\<^sub>1_evals\<^sub>1_inducts)
  case New\<^sub>1 thus ?case by (clarsimp simp add:blank_def fun_eq_iff)
next
  case NewFail\<^sub>1 thus ?case by(auto simp: handle_def pcs_def)
next
  case (Cast\<^sub>1 e h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 D fs C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc)#frs)" using Cast\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc+1)#frs)"
    using Cast\<^sub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc)#frs)"
    using CastNull\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc+1)#frs)"
    using CastNull\<^sub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastFail\<^sub>1 e h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 D fs C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt ClassCast"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc)#frs)"
    using CastFail\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Addr a#vs) ls\<^sub>1 ?pc frs"
    using CastFail\<^sub>1 by (auto simp add:handle_def cast_ok_def)
  also have "handle P C M ?xa h\<^sub>1 (Addr a#vs) ls\<^sub>1 ?pc frs =
             handle P C M ?xa h\<^sub>1 vs ls\<^sub>1 ?pc frs"
    using CastFail\<^sub>1.prems by(auto simp:handle_Cons)
  finally have exec: "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow> \<dots>".
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>1. ?H pc\<^sub>1))")
  proof
    show ?N by simp
  next
    have "?eq \<longrightarrow> ?H ?pc" using exec by auto
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>1. ?H pc\<^sub>1)" by blast
  qed
next
  case CastThrow\<^sub>1 thus ?case by fastforce
next
  case Val\<^sub>1 thus ?case by simp
next
  case Var\<^sub>1 thus ?case by auto
next
  case (BinOp\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 e\<^sub>2 v\<^sub>2 h\<^sub>2 ls\<^sub>2 bop w)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 (Val v\<^sub>2) h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 v\<^sub>2 xa (v\<^sub>1#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)" using BinOp\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v\<^sub>2#v\<^sub>1#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
    using BinOp\<^sub>1.prems IH\<^sub>2 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#vs,ls\<^sub>2,C,M,?pc\<^sub>2+1)#frs)"
    using BinOp\<^sub>1 by(cases bop) auto
  finally show ?case by (auto split: bop.splits simp:add.assoc)
next
  case BinOpThrow\<^sub>1\<^sub>1 thus ?case by(fastforce)
next
  case (BinOpThrow\<^sub>2\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 e\<^sub>2 e h\<^sub>2 ls\<^sub>2 bop)
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc)#frs)"
  have 1: "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow> ?\<sigma>\<^sub>1"
    using BinOpThrow\<^sub>2\<^sub>1 by fastforce
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 (throw e) h\<^sub>2 ls\<^sub>2 C M ?pc v xa (v\<^sub>1#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc + size(compE\<^sub>2 e\<^sub>2) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (v\<^sub>1#vs) ls\<^sub>2 pc\<^sub>2 frs"
        using BinOpThrow\<^sub>2\<^sub>1.prems by fastforce
      have 3: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using 2 BinOpThrow\<^sub>2\<^sub>1.prems pc\<^sub>2 by(auto simp:handle_Cons)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 3] by auto
      hence "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)" by iprover
  qed
next
  case (FAcc\<^sub>1 e h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 C fs F D w)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc)#frs)" using FAcc\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc+1)#frs)"
    using FAcc\<^sub>1 by auto
  finally show ?case by auto
next
  case (FAccNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 F D)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc)#frs)" using FAccNull\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc frs"
    using FAccNull\<^sub>1.prems
    by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc frs =
             handle P C M ?xa h\<^sub>1 vs ls\<^sub>1 ?pc frs"
    using FAccNull\<^sub>1.prems by(auto simp add:handle_Cons)
  finally show ?case by (auto intro: exI[where x = ?pc])
next
  case FAccThrow\<^sub>1 thus ?case by fastforce
next
  case (LAss\<^sub>1 e h\<^sub>0 ls\<^sub>0 w h\<^sub>1 ls\<^sub>1 i ls\<^sub>2)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc)#frs)" using LAss\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Unit#vs,ls\<^sub>2,C,M,?pc+2)#frs)"
    using LAss\<^sub>1 by auto
  finally show ?case using LAss\<^sub>1 by auto
next
  case LAssThrow\<^sub>1 thus ?case by fastforce
next
  case (FAss\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 C fs fs' F D h\<^sub>2')
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 w xa (Addr a#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)" using FAss\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Addr a#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
    using FAss\<^sub>1.prems IH\<^sub>2 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2',(Unit#vs,ls\<^sub>2,C,M,?pc\<^sub>2+2)#frs)"
    using FAss\<^sub>1 by auto
  finally show ?case using FAss\<^sub>1 by (auto simp:add.assoc)
next
  case (FAssNull\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 F D)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 w xa (Null#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)" using FAssNull\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Null#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
    using FAssNull\<^sub>1.prems IH\<^sub>2 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (w#Null#vs) ls\<^sub>2 ?pc\<^sub>2 frs"
    using FAssNull\<^sub>1.prems
    by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^sub>2 (w#Null#vs) ls\<^sub>2 ?pc\<^sub>2 frs =
             handle P C M ?xa h\<^sub>2 vs ls\<^sub>2 ?pc\<^sub>2 frs"
    using FAssNull\<^sub>1.prems by(auto simp add:handle_Cons)
  finally show ?case by (auto intro: exI[where x = ?pc\<^sub>2])
next
  case (FAssThrow\<^sub>2\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 w h\<^sub>1 ls\<^sub>1 e\<^sub>2 e' h\<^sub>2 ls\<^sub>2 F D)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
  have 1: "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow> ?\<sigma>\<^sub>1"
    using FAssThrow\<^sub>2\<^sub>1 by fastforce
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 (throw e') h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 v xa (w#vs) frs
                    (I - pcs (compxE\<^sub>2 e\<^sub>1 pc (length vs)))" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1 + size(compE\<^sub>2 e\<^sub>2) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1 (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (w#vs) ls\<^sub>2 pc\<^sub>2 frs"
        using FAssThrow\<^sub>2\<^sub>1.prems by fastforce
      have 3: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using 2 FAssThrow\<^sub>2\<^sub>1.prems pc\<^sub>2 by(auto simp:handle_Cons)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 3] by auto
      hence "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)" by iprover
  qed
next
  case FAssThrow\<^sub>1\<^sub>1 thus ?case by fastforce
next
  case (Call\<^sub>1 e h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 Ca fs M' Ts T body D ls\<^sub>2' f h\<^sub>3 ls\<^sub>3)
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs, ls\<^sub>0, C,M,pc)#frs)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(Addr a # vs, ls\<^sub>1, C,M,?pc\<^sub>1)#frs)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?frs\<^sub>2 = "(rev pvs @ Addr a # vs, ls\<^sub>2, C,M,?pc\<^sub>2)#frs"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2)"
  let ?frs\<^sub>2' = "([], ls\<^sub>2', D,M',0) # ?frs\<^sub>2"
  let ?\<sigma>\<^sub>2' = "(None, h\<^sub>2, ?frs\<^sub>2')"
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 pvs xa
                    (map Val pvs) (Addr a # vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Call\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es Call\<^sub>1.prems by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2'"
    using Call\<^sub>1 by(auto simp add: nth_append compMb\<^sub>2_def)
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>2'".
  have "P\<^sub>1 \<turnstile> Ca sees M': Ts\<rightarrow>T = body in D" by fact
  then have M'_in_D: "P\<^sub>1 \<turnstile> D sees M': Ts\<rightarrow>T = body in D"
    by(rule sees_method_idemp) 
  hence M'_code: "compP\<^sub>2 P\<^sub>1,D,M',0 \<rhd> compE\<^sub>2 body @ [Return]"
    and M'_xtab: "compP\<^sub>2 P\<^sub>1,D,M' \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
    by(rule beforeM, rule beforexM)
  have IH_body: "PROP ?P body h\<^sub>2 ls\<^sub>2' f h\<^sub>3 ls\<^sub>3 D M' 0 v xa [] ?frs\<^sub>2 ({..<size(compE\<^sub>2 body)})" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow>
                     (None,h\<^sub>3,([v],ls\<^sub>3,D,M',size(compE\<^sub>2 body))#?frs\<^sub>2)"
        using val IH_body Call\<^sub>1.prems M'_code M'_xtab
        by (fastforce simp del:split_paired_Ex)
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, (v # vs, ls\<^sub>2, C,M,?pc\<^sub>2+1)#frs)"
        using Call\<^sub>1 M'_code M'_in_D by(auto simp: nth_append compMb\<^sub>2_def)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      with IH_body obtain pc\<^sub>2 where
        pc\<^sub>2: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < size(compE\<^sub>2 body) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 body 0 0)" and
        2: "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> handle P D M' xa h\<^sub>3 [] ls\<^sub>3 pc\<^sub>2 ?frs\<^sub>2"
        using Call\<^sub>1.prems M'_code M'_xtab
        by (fastforce simp del:split_paired_Ex)
      have "handle P D M' xa h\<^sub>3 [] ls\<^sub>3 pc\<^sub>2 ?frs\<^sub>2 =
            handle P C M xa h\<^sub>3 (rev pvs @ Addr a # vs) ls\<^sub>2 ?pc\<^sub>2 frs"
        using pc\<^sub>2 M'_in_D by(auto simp add:handle_def)
      also have "\<dots> = handle P C M xa h\<^sub>3 vs ls\<^sub>2 ?pc\<^sub>2 frs"
        using Call\<^sub>1.prems by(auto simp add:handle_append handle_Cons)
      finally have "?H ?pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (CallParamsThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 w h\<^sub>1 ls\<^sub>1 es es' h\<^sub>2 ls\<^sub>2 pvs ex es'' M')
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs, ls\<^sub>0, C,M,pc)#frs)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(w # vs, ls\<^sub>1, C,M,?pc\<^sub>1)#frs)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using CallParamsThrow\<^sub>1 by fastforce
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?Ps es h\<^sub>1 ls\<^sub>1 es' h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 pvs xa es'' (w#vs) frs
        (I - pcs (compxE\<^sub>2 e pc (length vs)))" by fact
      ultimately have "\<exists>pc\<^sub>2.
        (?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1 + size(compEs\<^sub>2 es) \<and>
         \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxEs\<^sub>2 es ?pc\<^sub>1 (size vs + 1))) \<and>
        P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (w#vs) ls\<^sub>2 pc\<^sub>2 frs"
        (is "\<exists>pc\<^sub>2. ?PC pc\<^sub>2 \<and> ?Exec pc\<^sub>2")
        using CallParamsThrow\<^sub>1 by force
      then obtain pc\<^sub>2 where pc\<^sub>2: "?PC pc\<^sub>2" and 2: "?Exec pc\<^sub>2" by iprover
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 2] CallParamsThrow\<^sub>1
        by(auto simp:handle_Cons)
      hence "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)" by iprover
  qed
next
  case (CallNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 M')
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 pvs xa
                    (map Val pvs) (Null#vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)" using CallNull\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(rev pvs@Null#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
    using CallNull\<^sub>1 IH_es by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@Null#vs) ls\<^sub>2 ?pc\<^sub>2 frs"
    using CallNull\<^sub>1.prems
    by(auto simp:split_beta handle_def nth_append simp del: split_paired_Ex)
  also have "handle P C M ?xa h\<^sub>2 (rev pvs@Null#vs) ls\<^sub>2 ?pc\<^sub>2 frs =
             handle P C M ?xa h\<^sub>2 vs ls\<^sub>2 ?pc\<^sub>2 frs"
    using CallNull\<^sub>1.prems by(auto simp:handle_Cons handle_append)
  finally show ?case by (auto intro: exI[where x = ?pc\<^sub>2])
next
  case CallObjThrow\<^sub>1 thus ?case by fastforce
next
  case Block\<^sub>1 thus ?case by auto
next
  case (Seq\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 w h\<^sub>1 ls\<^sub>1 e\<^sub>2 e\<^sub>2' h\<^sub>2 ls\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
    using Seq\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Seq\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>2 = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>2)"
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 e\<^sub>2' h\<^sub>2 ls\<^sub>2 C M (?pc\<^sub>1+1) v xa vs frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
        using val Seq\<^sub>1.prems IH\<^sub>2 by fastforce
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using IH\<^sub>2 Seq\<^sub>1.prems by fastforce
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case SeqThrow\<^sub>1 thus ?case by fastforce
next
  case (CondT\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 e\<^sub>1 e' h\<^sub>2 ls\<^sub>2 e\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(True)#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
    using CondT\<^sub>1 by (fastforce simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using CondT\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2' = "?pc\<^sub>1' + 1 + length(compE\<^sub>2 e\<^sub>2)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>1')#frs)"
        using val CondT\<^sub>1 by(fastforce simp:Int_Un_distrib)
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2')#frs)"
        using CondT\<^sub>1 by(auto simp:add.assoc)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      let ?d = "size vs"
      let ?I = "I - pcs(compxE\<^sub>2 e pc ?d) - pcs(compxE\<^sub>2 e\<^sub>2 (?pc\<^sub>1'+1) ?d)"
      assume throw: ?throw
      moreover
      have "PROP ?P e\<^sub>1 h\<^sub>1 ls\<^sub>1 e' h\<^sub>2 ls\<^sub>2 C M (?pc\<^sub>1+1) v xa vs frs ?I" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>1 (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using CondT\<^sub>1.prems by (fastforce simp:Int_Un_distrib)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (CondF\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 e\<^sub>2 e' h\<^sub>2 ls\<^sub>2 e\<^sub>1)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>1)+ 1"
  let ?pc\<^sub>2' = "?pc\<^sub>2 + length(compE\<^sub>2 e\<^sub>2)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>2)#frs)"
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(False)#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
    using CondF\<^sub>1 by (fastforce simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using CondF\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2')#frs)"
        using val CondF\<^sub>1 by(fastforce simp:Int_Un_distrib)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      let ?d = "size vs"
      let ?I = "I - pcs(compxE\<^sub>2 e pc ?d) - pcs(compxE\<^sub>2 e\<^sub>1 (?pc\<^sub>1+1) ?d)"
      assume throw: ?throw
      moreover
      have "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 e' h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>2 v xa vs frs ?I" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>2 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>2 ?d)" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using CondF\<^sub>1.prems by(fastforce simp:Int_Un_distrib)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (CondThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 f h\<^sub>1 ls\<^sub>1 e\<^sub>1 e\<^sub>2)
  let ?d = "size vs"
  let ?xt\<^sub>1 = "compxE\<^sub>2 e\<^sub>1 (pc+size(compE\<^sub>2 e)+1) ?d"
  let ?xt\<^sub>2 = "compxE\<^sub>2 e\<^sub>2 (pc+size(compE\<^sub>2 e)+size(compE\<^sub>2 e\<^sub>1)+2) ?d"
  let ?I = "I - (pcs ?xt\<^sub>1 \<union> pcs ?xt\<^sub>2)"
  have "pcs(compxE\<^sub>2 e pc ?d) \<inter> pcs(?xt\<^sub>1 @ ?xt\<^sub>2) = {}"
    using CondThrow\<^sub>1.prems by (simp add:Int_Un_distrib)
  moreover have "PROP ?P e h\<^sub>0 ls\<^sub>0 (throw f) h\<^sub>1 ls\<^sub>1 C M pc v xa vs frs ?I" by fact
  ultimately show ?case using CondThrow\<^sub>1.prems by fastforce
next
  case (WhileF\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 c)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?pc' = "?pc + length(compE\<^sub>2 c) + 3"
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
            (None,h\<^sub>1,(Bool False#vs,ls\<^sub>1,C,M,?pc)#frs)"
    using WhileF\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc')#frs)"
    using WhileF\<^sub>1 by (auto simp:add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Unit#vs,ls\<^sub>1,C,M,?pc'+1)#frs)"
    using WhileF\<^sub>1.prems by (auto simp:eval_nat_numeral)
  finally show ?case by (simp add:add.assoc eval_nat_numeral)
next
  case (WhileT\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 c v\<^sub>1 h\<^sub>2 ls\<^sub>2 e\<^sub>3 h\<^sub>3 ls\<^sub>3)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?pc' = "?pc + length(compE\<^sub>2 c) + 1"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,(vs,ls\<^sub>2,C,M,pc)#frs)"
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool True#vs,ls\<^sub>1,C,M,?pc)#frs)"
    using WhileT\<^sub>1 by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc+1)#frs)"
    using WhileT\<^sub>1.prems by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v\<^sub>1#vs,ls\<^sub>2,C,M,?pc')#frs)"
    using WhileT\<^sub>1 by(fastforce)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using WhileT\<^sub>1.prems by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>2".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>2 -jvm\<rightarrow> (None,h\<^sub>3,(v#vs,ls\<^sub>3,C,M,?pc'+3)#frs)"
        using val WhileT\<^sub>1 by (auto simp add:add.assoc eval_nat_numeral)
      finally show ?trans by(simp add:add.assoc eval_nat_numeral)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P (while (e) c) h\<^sub>2 ls\<^sub>2 e\<^sub>3 h\<^sub>3 ls\<^sub>3 C M pc v xa vs frs I" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "pc \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc'+3 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 (while (e) c) pc (size vs))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>2 -jvm\<rightarrow> handle P C M xa h\<^sub>3 vs ls\<^sub>3 pc\<^sub>2 frs"
        using WhileT\<^sub>1.prems by (auto simp:add.assoc eval_nat_numeral)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case WhileCondThrow\<^sub>1 thus ?case by fastforce
next
  case (WhileBodyThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1 c e' h\<^sub>2 ls\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1)#frs)"
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(True)#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
    using WhileBodyThrow\<^sub>1 by (fastforce simp add: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using  WhileBodyThrow\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 c)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P c h\<^sub>1 ls\<^sub>1 (throw e') h\<^sub>2 ls\<^sub>2 C M (?pc\<^sub>1+1) v xa vs frs
                    (I - pcs (compxE\<^sub>2 e pc (size vs)))" by fact
      ultimately obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 c (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using WhileBodyThrow\<^sub>1.prems by (fastforce simp:Int_Un_distrib)
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by auto
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (Throw\<^sub>1 e h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1)
  let ?pc = "pc + size(compE\<^sub>2 e)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>1. ?H pc\<^sub>1)")
    proof
      assume ?throw
      hence "P \<turnstile> (None, h\<^sub>0, (vs, ls\<^sub>0, C, M, pc) # frs) -jvm\<rightarrow>
                 (None, h\<^sub>1, (Addr xa#vs, ls\<^sub>1, C, M, ?pc) # frs)"
        using Throw\<^sub>1 by fastforce
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M xa h\<^sub>1 (Addr xa#vs) ls\<^sub>1 ?pc frs"
        using Throw\<^sub>1.prems by(auto simp add:handle_def)
      also have "handle P C M xa h\<^sub>1 (Addr xa#vs) ls\<^sub>1 ?pc frs =
                 handle P C M xa h\<^sub>1 vs ls\<^sub>1 ?pc frs"
        using Throw\<^sub>1.prems by(auto simp add:handle_Cons)
      finally have "?H ?pc" by simp
      thus "\<exists>pc\<^sub>1. ?H pc\<^sub>1" by iprover
    qed
  qed
next
  case (ThrowNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 h\<^sub>1 ls\<^sub>1)
  let ?pc = "pc + size(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>1. ?H pc\<^sub>1)")
    proof
      assume throw: ?throw
      have "P \<turnstile> (None, h\<^sub>0, (vs, ls\<^sub>0, C, M, pc) # frs) -jvm\<rightarrow>
                 (None, h\<^sub>1, (Null#vs, ls\<^sub>1, C, M, ?pc) # frs)"
        using ThrowNull\<^sub>1 by fastforce
      also have "P \<turnstile> \<dots> -jvm\<rightarrow>  handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc frs"
        using ThrowNull\<^sub>1.prems by(auto simp add:handle_def)
      also have "handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc frs =
                 handle P C M ?xa h\<^sub>1 vs ls\<^sub>1 ?pc frs"
        using ThrowNull\<^sub>1.prems by(auto simp add:handle_Cons)
      finally have "?H ?pc" using throw by simp
      thus "\<exists>pc\<^sub>1. ?H pc\<^sub>1" by iprover
    qed
  qed
next
  case ThrowThrow\<^sub>1 thus ?case by fastforce
next
  case (Try\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 Ci i e\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 2 + length(compE\<^sub>2 e\<^sub>2)"
  have "P,C,M \<rhd> compxE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2) pc (size vs) / I,size vs" by fact
  hence "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs) /
                 {pc..<pc + length (compE\<^sub>2 e\<^sub>1)},size vs"
    using Try\<^sub>1.prems by (fastforce simp:beforex_def split:if_split_asm)
  hence "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs) -jvm\<rightarrow>
             (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)" using Try\<^sub>1 by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1')#frs)"
    using Try\<^sub>1.prems by auto
  finally show ?case by (auto simp:add.assoc)
next
  case (TryCatch\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 D fs Ci i e\<^sub>2 e\<^sub>2' h\<^sub>2 ls\<^sub>2)
  let ?e = "try e\<^sub>1 catch(Ci i) e\<^sub>2"
  let ?xt = "compxE\<^sub>2 ?e pc (size vs)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?ls\<^sub>1 = "ls\<^sub>1[i := Addr a]"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 2"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,?ls\<^sub>1,C,M, ?pc\<^sub>1') # frs)"
  have I: "{pc..<pc + length (compE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" by fact+
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,((Addr a)#vs,ls\<^sub>1,C,M, ?pc\<^sub>1+1) # frs)"
  proof -
    have "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 (Throw a) h\<^sub>1 ls\<^sub>1 C M pc w a vs frs {pc..<pc + length (compE\<^sub>2 e\<^sub>1)}"
      by fact
    moreover have "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs)/{pc..<?pc\<^sub>1},size vs"
      using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < ?pc\<^sub>1 \<and>
             \<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs)) \<and>
             P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs"
      using  TryCatch\<^sub>1.prems by auto
    then obtain pc\<^sub>1 where
      pc\<^sub>1_in_e\<^sub>1: "pc \<le> pc\<^sub>1" "pc\<^sub>1 < ?pc\<^sub>1" and
      pc\<^sub>1_not_caught: "\<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs" by iprover
    from beforex obtain xt\<^sub>0 xt\<^sub>1
      where ex_tab: "ex_table_of P C M = xt\<^sub>0 @ ?xt @ xt\<^sub>1"
      and disj: "pcs xt\<^sub>0 \<inter> I = {}" by(auto simp:beforex_def)
    have hp: "h\<^sub>1 a = Some (D, fs)" "P\<^sub>1 \<turnstile> D \<preceq>\<^sup>* Ci" by fact+
    have "pc\<^sub>1 \<notin> pcs xt\<^sub>0" using pc\<^sub>1_in_e\<^sub>1 I disj by auto
    with pc\<^sub>1_in_e\<^sub>1 pc\<^sub>1_not_caught hp
    show ?thesis using ex_tab 0 by(simp add:handle_def matches_ex_entry_def)
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using TryCatch\<^sub>1 by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" .
  let ?pc\<^sub>2 = "?pc\<^sub>1' + length(compE\<^sub>2 e\<^sub>2)"
  let ?I\<^sub>2 = "{?pc\<^sub>1' ..< ?pc\<^sub>2}"
  have "P,C,M \<rhd> compxE\<^sub>2 ?e pc (size vs) / I,size vs" by fact
  hence beforex\<^sub>2: "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1' (size vs) / ?I\<^sub>2, size vs"
    using I pcs_subset[of _ ?pc\<^sub>1'] by(auto elim!:beforex_appendD2)
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ?ls\<^sub>1 e\<^sub>2' h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1' v xa vs frs ?I\<^sub>2" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1 also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
        using val beforex\<^sub>2 IH\<^sub>2 TryCatch\<^sub>1.prems by auto
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1+2 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1' (size vs))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 vs ls\<^sub>2 pc\<^sub>2 frs"
        using IH\<^sub>2 beforex\<^sub>2 TryCatch\<^sub>1.prems by auto
      have "?H pc\<^sub>2" using pc\<^sub>2 jvm_trans[OF 1 2]
        by (simp add:match_ex_entry) (fastforce)
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (TryThrow\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 a h\<^sub>1 ls\<^sub>1 D fs Ci i e\<^sub>2)
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?e = "try e\<^sub>1 catch(Ci i) e\<^sub>2"
  let ?xt = "compxE\<^sub>2 ?e pc (size vs)"
  have I: "{pc..<pc + length (compE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" by fact+
  have "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 (Throw a) h\<^sub>1 ls\<^sub>1 C M pc w a vs frs {pc..<pc + length (compE\<^sub>2 e\<^sub>1)}" by fact
  moreover have "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs)/{pc..<?pc\<^sub>1},size vs"
    using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < ?pc\<^sub>1 \<and>
             \<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs)) \<and>
             P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs"
      using TryThrow\<^sub>1.prems by auto
    then obtain pc\<^sub>1 where
      pc\<^sub>1_in_e\<^sub>1: "pc \<le> pc\<^sub>1" "pc\<^sub>1 < ?pc\<^sub>1" and
      pc\<^sub>1_not_caught: "\<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 vs ls\<^sub>1 pc\<^sub>1 frs" by iprover
  show ?case (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      with TryThrow\<^sub>1 pc\<^sub>1_in_e\<^sub>1 pc\<^sub>1_not_caught 0
      have "?H pc\<^sub>1" by (simp add:match_ex_entry) auto
      hence "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)" by iprover
  qed
next
  case Nil\<^sub>1 thus ?case by simp
next
  case (Cons\<^sub>1 e h\<^sub>0 ls\<^sub>0 v h\<^sub>1 ls\<^sub>1 es fs h\<^sub>2 ls\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc)#frs)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,?pc\<^sub>1)#frs)"
  have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Cons\<^sub>1 by fastforce
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  have IHs: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 fs h\<^sub>2 ls\<^sub>2 C M ?pc\<^sub>1 (tl ws) xa es' (v#vs) frs
    (I - pcs (compxE\<^sub>2 e pc (length vs)))" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(rev(ws) @ vs,ls\<^sub>2,C,M,?pc\<^sub>2)#frs)"
        using val IHs Cons\<^sub>1.prems by fastforce
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 where
        pc\<^sub>2: "?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxEs\<^sub>2 es ?pc\<^sub>1 (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (v#vs) ls\<^sub>2 pc\<^sub>2 frs"
        using IHs Cons\<^sub>1.prems
        by(fastforce simp:Cons_eq_append_conv neq_Nil_conv)
      have "?H pc\<^sub>2" using Cons\<^sub>1.prems pc\<^sub>2 jvm_trans[OF 1 2]
        by (auto simp add: handle_Cons)
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case ConsThrow\<^sub>1 thus ?case by (fastforce simp:Cons_eq_append_conv)
qed
(*>*)


(*FIXME move! *)
lemma atLeast0AtMost[simp]: "{0::nat..n} = {..n}"
by auto

lemma atLeast0LessThan[simp]: "{0::nat..<n} = {..<n}"
by auto

fun exception :: "'a exp \<Rightarrow> addr option" where
  "exception (Throw a) = Some a"
| "exception e = None"


lemma comp\<^sub>2_correct:
assumes "method": "P\<^sub>1 \<turnstile> C sees M:Ts\<rightarrow>T = body in C"
    and eval:   "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>body,(h,ls)\<rangle> \<Rightarrow> \<langle>e',(h',ls')\<rangle>"
shows "compP\<^sub>2 P\<^sub>1 \<turnstile> (None,h,[([],ls,C,M,0)]) -jvm\<rightarrow> (exception e',h',[])"
(*<*)
      (is "_ \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1")
proof -
  let ?P = "compP\<^sub>2 P\<^sub>1"
  have code: "?P,C,M,0 \<rhd> compE\<^sub>2 body" using beforeM[OF "method"] by auto
  have xtab: "?P,C,M \<rhd> compxE\<^sub>2 body 0 (size[])/{..<size(compE\<^sub>2 body)},size[]"
    using beforexM[OF "method"] by auto
  \<comment> \<open>Distinguish if e' is a value or an exception\<close>
  { fix v assume [simp]: "e' = Val v"
    have "?P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h',[([v],ls',C,M,size(compE\<^sub>2 body))])"
      using Jcc[OF eval code xtab] by auto
    also have "?P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using beforeM[OF "method"] by auto
    finally have ?thesis .
  }
  moreover
  { fix a assume [simp]: "e' = Throw a"
    obtain pc where pc: "0 \<le> pc \<and> pc < size(compE\<^sub>2 body) \<and>
          \<not> caught ?P pc h' a (compxE\<^sub>2 body 0 0)"
    and 1: "?P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle ?P C M a h' [] ls' pc []"
      using Jcc[OF eval code xtab] by fastforce
    from pc have "handle ?P C M a h' [] ls' pc [] = ?\<sigma>\<^sub>1" using xtab "method"
      by(auto simp:handle_def compMb\<^sub>2_def)
    with 1 have ?thesis by simp
  } 
  ultimately show ?thesis using eval\<^sub>1_final[OF eval] by(auto simp:final_def)
qed
(*>*)

end
