section \<open>Generic Recursion Combinator for Complete Lattice Structured Domains\<close>
theory RefineG_Recursion
imports "../Refine_Misc" RefineG_Transfer RefineG_Domain
begin

text \<open>
  We define a recursion combinator that asserts monotonicity.
\<close>


(* TODO: Move to Domain.*)
text \<open>
  The following lemma allows to compare least fixed points wrt.\ different flat
  orderings. At any point, the fixed points are either equal or have their 
  orderings bottom values.
\<close>
lemma fp_compare:
  \<comment> \<open>At any point, fixed points wrt.\ different orderings are either equal, 
    or both bottom.\<close>
  assumes M1: "flatf_mono b1 B" and M2: "flatf_mono b2 B"
  shows "flatf_fp b1 B x = flatf_fp b2 B x 
    \<or> (flatf_fp b1 B x = b1 \<and> flatf_fp b2 B x = b2)"
proof -
  note UNF1 = flatf_ord.fixp_unfold[OF M1, symmetric]
  note UNF2 = flatf_ord.fixp_unfold[OF M2, symmetric]

  from UNF1 have 1: "flatf_ord b2 (B (flatf_fp b1 B)) (flatf_fp b1 B)" by simp
  from UNF2 have 2: "flatf_ord b1 (B (flatf_fp b2 B)) (flatf_fp b2 B)" by simp

  from flatf_ord.fixp_lowerbound[OF M2 1] flatf_ord.fixp_lowerbound[OF M1 2]
    show ?thesis unfolding fun_ord_def flat_ord_def by auto
qed

(* TODO: Move *)
lemma flat_ord_top[simp]: "flat_ord b b x" by (simp add: flat_ord_def)


(* TODO: Move to Domain.*)
lemma lfp_gfp_compare:
  \<comment> \<open>Least and greatest fixed point are either equal, or bot and top\<close>
  assumes MLE: "flatf_mono_le B" and MGE: "flatf_mono_ge B"
  shows "flatf_lfp B x = flatf_gfp B x 
    \<or> (flatf_lfp B x = bot \<and> flatf_gfp B x = top)"
  using fp_compare[OF MLE MGE] .


(* TODO: Move to Domain *)
definition trimono :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b::{bot,order,top})) \<Rightarrow> bool" 
  where "trimono B \<equiv> \<^cancel>\<open>flatf_mono_le B \<and>\<close> flatf_mono_ge B \<and> mono B"
lemma trimonoI[refine_mono]: 
  "\<lbrakk>flatf_mono_ge B; mono B\<rbrakk> \<Longrightarrow> trimono B"
  unfolding trimono_def by auto

lemma trimono_trigger: "trimono B \<Longrightarrow> trimono B" .

declaration \<open>Refine_Mono_Prover.declare_mono_triggers @{thms trimono_trigger}\<close>

(*lemma trimonoD_flatf_le: "trimono B \<Longrightarrow> flatf_mono_le B"
  unfolding trimono_def by auto*)

lemma trimonoD_flatf_ge: "trimono B \<Longrightarrow> flatf_mono_ge B"
  unfolding trimono_def by auto

lemma trimonoD_mono: "trimono B \<Longrightarrow> mono B"
  unfolding trimono_def by auto

lemmas trimonoD = trimonoD_flatf_ge trimonoD_mono

(* TODO: Optimize mono-prover to only do derivations once. 
  Will cause problem with higher-order unification on ord - variable! *)
definition "triords \<equiv> {flat_ge,(\<le>)}"
lemma trimono_alt: 
  "trimono B \<longleftrightarrow> (\<forall>ord\<in>fun_ord`triords. monotone ord ord B)"
  unfolding trimono_def
  by (auto simp: ccpo_mono_simp[symmetric] triords_def 
    fun_ord_def[abs_def] le_fun_def[abs_def])

lemma trimonoI': 
  assumes "\<And>ord. ord\<in>triords \<Longrightarrow> monotone (fun_ord ord) (fun_ord ord) B"
  shows "trimono B"
  unfolding trimono_alt using assms by blast


(* TODO: Once complete_lattice and ccpo typeclass are unified,
  we should also define a REC-combinator for ccpos! *)

definition REC where "REC B x \<equiv> 
  if (trimono B) then (lfp B x) else (top::'a::complete_lattice)"
definition RECT ("REC\<^sub>T") where "RECT B x \<equiv> 
  if (trimono B) then (flatf_gfp B x) else (top::'a::complete_lattice)"

lemma RECT_gfp_def: "RECT B x = 
  (if (trimono B) then (gfp B x) else (top::'a::complete_lattice))"
  unfolding RECT_def
  by (auto simp: gfp_eq_flatf_gfp[OF trimonoD_flatf_ge trimonoD_mono])

lemma REC_unfold: "trimono B \<Longrightarrow> REC B = B (REC B)"
  unfolding REC_def [abs_def]
  by (simp add: lfp_unfold[OF trimonoD_mono, symmetric])

lemma RECT_unfold: "\<lbrakk>trimono B\<rbrakk> \<Longrightarrow> RECT B = B (RECT B)"
  unfolding RECT_def [abs_def]
  by (simp add: flatf_ord.fixp_unfold[OF trimonoD_flatf_ge, symmetric])

lemma REC_mono[refine_mono]:
  assumes [simp]: "trimono B"
  assumes LE: "\<And>F x. (B F x) \<le> (B' F x)"
  shows "(REC B x) \<le> (REC B' x)"
  unfolding REC_def
  apply clarsimp
  apply (rule lfp_mono[THEN le_funD])
  apply (rule LE[THEN le_funI])
  done

lemma RECT_mono[refine_mono]:
  assumes [simp]: "trimono B'"
  assumes LE: "\<And>F x. flat_ge (B F x) (B' F x)"
  shows "flat_ge (RECT B x) (RECT B' x)"
  unfolding RECT_def
  apply clarsimp
  apply (rule flatf_fp_mono, (simp_all add: trimonoD) [2])
  apply (rule LE)
  done

lemma REC_le_RECT: "REC body x \<le> RECT body x"
  unfolding REC_def RECT_gfp_def
  apply (cases "trimono body")
  apply clarsimp
  apply (rule lfp_le_gfp[THEN le_funD])
  apply (simp add: trimonoD)
  apply simp
  done

print_statement flatf_fp_induct_pointwise
theorem lfp_induct_pointwise:
  fixes a::'a
  assumes ADM1: "\<And>a x. chain_admissible (\<lambda>b. \<forall>a x. pre a x \<longrightarrow> post a x (b x))"
  assumes ADM2: "\<And>a x. pre a x \<longrightarrow> post a x bot"
  assumes MONO: "mono B"
  assumes P0: "pre a x"
  assumes IS: 
    "\<And>f a x.
        \<lbrakk>\<And>a' x'. pre a' x' \<Longrightarrow> post a' x' (f x'); pre a x;
         f \<le> (lfp B)\<rbrakk>
        \<Longrightarrow> post a x (B f x)"
  shows "post a x (lfp B x)"
proof -
  define u where "u = lfp B"

  have [simp]: "\<And>f. f\<le>lfp B \<Longrightarrow> B f \<le> lfp B"
    by (metis (poly_guards_query) MONO lfp_unfold monoD)

  have "(\<forall>a x. pre a x \<longrightarrow> post a x (lfp B x)) \<and> lfp B \<le> u"
    apply (rule lfp_cadm_induct[where f=B])
    apply (rule admissible_conj)
    apply (rule ADM1)
    apply (rule)
    apply (blast intro: Sup_least)
    apply (simp add: le_fun_def ADM2) []
    apply fact
    apply (intro conjI allI impI)
    unfolding u_def
    apply (blast intro: IS)
    apply simp
    done
  with P0 show ?thesis by blast
qed


lemma REC_rule_arb:
  fixes x::"'x" and arb::'arb
  assumes M: "trimono body"
  assumes I0: "pre arb x"
  assumes IS: "\<And>f arb x. \<lbrakk>
    \<And>arb' x. pre arb' x \<Longrightarrow> f x \<le> M arb' x; pre arb x; f \<le> REC body
  \<rbrakk> \<Longrightarrow> body f x \<le> M arb x"
  shows "REC body x \<le> M arb x"
  unfolding REC_def
  apply (clarsimp simp: M)
  apply (rule lfp_induct_pointwise[where pre=pre])
  apply (auto intro!: chain_admissibleI SUP_least) [2]
  apply (simp add: trimonoD[OF M])
  apply (rule I0)
  apply (rule IS, assumption+)
  apply (auto simp: REC_def[abs_def] intro!: le_funI dest: le_funD) []
  done

lemma RECT_rule_arb:
  assumes M: "trimono body"
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "pre (arb::'arb) (x::'x)"
  assumes IS: "\<And>f arb x. \<lbrakk> 
      \<And>arb' x'. \<lbrakk>pre arb' x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le> M arb' x'; 
      pre arb x;
      RECT body = f
    \<rbrakk>  \<Longrightarrow> body f x \<le> M arb x"
  shows "RECT body x \<le> M arb x"
  apply (rule wf_fixp_induct[where fp=RECT and pre=pre and B=body])
  apply (rule RECT_unfold)
  apply (simp_all add: M) [2]
  apply (rule WF)
  apply fact
  apply (rule IS)
  apply assumption
  apply assumption
  apply assumption
  done

lemma REC_rule:
  fixes x::"'x"
  assumes M: "trimono body"
  assumes I0: "pre x"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x. pre x \<Longrightarrow> f x \<le> M x; pre x; f \<le> REC body \<rbrakk> 
    \<Longrightarrow> body f x \<le> M x"
  shows "REC body x \<le> M x"
  by (rule REC_rule_arb[where pre="\<lambda>_. pre" and M="\<lambda>_. M", OF assms])
    
    
lemma RECT_rule:
  assumes M: "trimono body"
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "pre (x::'x)"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x'. \<lbrakk>pre x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le> M x'; pre x; 
                        RECT body = f
    \<rbrakk> \<Longrightarrow> body f x \<le> M x"
  shows "RECT body x \<le> M x"
  by (rule RECT_rule_arb[where pre="\<lambda>_. pre" and M="\<lambda>_. M", OF assms])




(* TODO: Can we set-up induction method to work with such goals? *)
lemma REC_rule_arb2:
  assumes M: "trimono body"
  assumes I0: "pre (arb::'arb) (arc::'arc) (x::'x)"
  assumes IS: "\<And>f arb arc x. \<lbrakk> 
      \<And>arb' arc' x'. \<lbrakk>pre arb' arc' x' \<rbrakk> \<Longrightarrow> f x' \<le> M arb' arc' x'; 
      pre arb arc x
    \<rbrakk>  \<Longrightarrow> body f x \<le> M arb arc x"
  shows "REC body x \<le> M arb arc x"
  apply (rule order_trans)
  apply (rule REC_rule_arb[
    where pre="case_prod pre" and M="case_prod M" and arb="(arb, arc)", 
    OF M])
  by (auto intro: assms)

lemma REC_rule_arb3:
  assumes M: "trimono body"
  assumes I0: "pre (arb::'arb) (arc::'arc) (ard::'ard) (x::'x)"
  assumes IS: "\<And>f arb arc ard x. \<lbrakk> 
      \<And>arb' arc' ard' x'. \<lbrakk>pre arb' arc' ard' x'\<rbrakk> \<Longrightarrow> f x' \<le> M arb' arc' ard' x';
      pre arb arc ard x 
    \<rbrakk>  \<Longrightarrow> body f x \<le> M arb arc ard x"
  shows "REC body x \<le> M arb arc ard x"
  apply (rule order_trans)
  apply (rule REC_rule_arb2[
    where pre="case_prod pre" and M="case_prod M" and arb="(arb, arc)" and arc="ard", 
    OF M])
  by (auto intro: assms)

lemma RECT_rule_arb2:
  assumes M: "trimono body"
  assumes WF: "wf (V::'x rel)"
  assumes I0: "pre (arb::'arb) (arc::'arc) (x::'x)"
  assumes IS: "\<And>f arb arc x. \<lbrakk> 
      \<And>arb' arc' x'. \<lbrakk>pre arb' arc' x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le> M arb' arc' x'; 
      pre arb arc x;
      f \<le> RECT body
    \<rbrakk>  \<Longrightarrow> body f x \<le> M arb arc x"
  shows "RECT body x \<le> M arb arc x"
  apply (rule order_trans)
  apply (rule RECT_rule_arb[
    where pre="case_prod pre" and M="case_prod M" and arb="(arb, arc)", 
    OF M WF])
  by (auto intro: assms)

lemma RECT_rule_arb3:
  assumes M: "trimono body"
  assumes WF: "wf (V::'x rel)"
  assumes I0: "pre (arb::'arb) (arc::'arc) (ard::'ard) (x::'x)"
  assumes IS: "\<And>f arb arc ard x. \<lbrakk> 
      \<And>arb' arc' ard' x'. \<lbrakk>pre arb' arc' ard' x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le> M arb' arc' ard' x'; 
    pre arb arc ard x;
    f \<le> RECT body
  \<rbrakk>  \<Longrightarrow> body f x \<le> M arb arc ard x"
  shows "RECT body x \<le> M arb arc ard x"
  apply (rule order_trans)
  apply (rule RECT_rule_arb2[
    where pre="case_prod pre" and M="case_prod M" and arb="(arb, arc)" and arc="ard", 
    OF M WF])
  by (auto intro: assms)



(* Obsolete, provide a variant to show nofail.
text {* The following lemma shows that greatest and least fixed point are equal,
  if we can provide a variant. *}
lemma RECT_eq_REC:
  assumes MONO: "flatf_mono_le body"
  assumes MONO_GE: "flatf_mono_ge body"
  assumes WF: "wf V"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> 
    body (\<lambda>x'. if (I x' \<and> (x',x)\<in>V) then f x' else top) x \<le> body f x"
  shows "RECT body x = REC body x"
  unfolding RECT_def REC_def 
proof (simp add: MONO MONO_GE)
  have "I x \<longrightarrow> flatf_gfp body x \<le> flatf_lfp body x"
    using WF
    apply (induct rule: wf_induct_rule)
    apply (rule impI)
    apply (subst flatf_ord.fixp_unfold[OF MONO])
    apply (subst flatf_ord.fixp_unfold[OF MONO_GE])
    apply (rule order_trans[OF _ IS])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    done
  


  from lfp_le_gfp' MONO have "lfp body x \<le> gfp body x" .
  moreover have "I x \<longrightarrow> gfp body x \<le> lfp body x"
    using WF
    apply (induct rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (subst lfp_unfold[OF MONO])
    apply (subst gfp_unfold[OF MONO])
    apply (rule order_trans[OF _ IS])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    done
  ultimately show ?thesis
    unfolding REC_def RECT_def gfp_eq_flatf_gfp[OF MONO_GE MONO, symmetric]
    apply (rule_tac antisym)
    using I0 MONO MONO_GE by auto
qed
*)

lemma RECT_eq_REC: 
  \<comment> \<open>Partial and total correct recursion are equal if total 
    recursion does not fail.\<close>
  assumes NT: "RECT body x \<noteq> top"
  shows "RECT body x = REC body x"
proof (cases "trimono body")
  case M: True 
  show ?thesis
    using NT M
    unfolding RECT_def REC_def
  proof clarsimp
    from lfp_unfold[OF trimonoD_mono[OF M], symmetric]
    have "flatf_ge (body (lfp body)) (lfp body)" by simp
    note flatf_ord.fixp_lowerbound[
      OF trimonoD_flatf_ge[OF M], of "lfp body", OF this]
    moreover assume "flatf_gfp body x \<noteq> top"
    ultimately show "flatf_gfp body x = lfp body x"
      by (auto simp add: fun_ord_def flat_ord_def)
  qed
next
  case False thus ?thesis unfolding RECT_def REC_def by auto
qed

lemma RECT_eq_REC_tproof:
  \<comment> \<open>Partial and total correct recursion are equal if we can provide a 
    termination proof.\<close>
  fixes a :: 'a
  assumes M: "trimono body"
  assumes WF: "wf V"
  assumes I0: "pre a x"
  assumes IS: "\<And>f arb x.
          \<lbrakk>\<And>arb' x'. \<lbrakk>pre arb' x'; (x', x) \<in> V\<rbrakk> \<Longrightarrow> f x' \<le> M arb' x'; 
            pre arb x; REC\<^sub>T body = f\<rbrakk>
          \<Longrightarrow> body f x \<le> M arb x"
  assumes NT: "M a x \<noteq> top"
  shows "RECT body x = REC body x \<and> RECT body x \<le> M a x"
proof
  show "RECT body x \<le> M a x"
    by (rule RECT_rule_arb[OF M WF, where pre=pre, OF I0 IS])
  
  with NT have "RECT body x \<noteq> top" by (metis top.extremum_unique)
  thus "RECT body x = REC body x" by (rule RECT_eq_REC)
qed


subsection \<open>Transfer\<close>

lemma (in transfer) transfer_RECT'[refine_transfer]:
  assumes REC_EQ: "\<And>x. fr x = b fr x"
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  shows "\<alpha> (fr x) \<le> RECT B x"
  unfolding RECT_def
proof clarsimp
  assume MONO: "trimono B"
  show "\<alpha> (fr x) \<le> flatf_gfp B x"
    apply (rule flatf_fixp_transfer[where B=B and fp'=fr and P="(=)", 
        OF _ trimonoD_flatf_ge[OF MONO]])
    apply simp
    apply (rule ext, fact)
    apply (simp)
    apply (simp,rule REF, blast)    
    done
qed

lemma (in ordered_transfer) transfer_RECT[refine_transfer]:
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  assumes M: "trimono b"
  shows "\<alpha> (RECT b x) \<le> RECT B x"
  apply (rule transfer_RECT')
  apply (rule RECT_unfold[OF M, THEN fun_cong])
  by fact

lemma (in dist_transfer) transfer_REC[refine_transfer]:
  assumes REF: "\<And>F f x. \<lbrakk>\<And>x. \<alpha> (f x) \<le> F x \<rbrakk> \<Longrightarrow> \<alpha> (b f x) \<le> B F x"
  assumes M: "trimono b"
  shows "\<alpha> (REC b x) \<le> REC B x"
  unfolding REC_def
  (* TODO: Clean up *)
  apply (clarsimp simp: M)
  apply (rule lfp_induct_pointwise[where B=b and pre="(=)"])
  apply (rule)
  apply clarsimp
  apply (subst \<alpha>_dist)
  apply (auto simp add: chain_def le_fun_def) []
  apply (rule Sup_least)
  apply auto []
  apply simp
  apply (simp add: trimonoD[OF M])
  apply (rule refl)
  apply (subst lfp_unfold)
  apply (simp add: trimonoD)
  apply (rule REF)
  apply blast
  done

(* TODO: Could we base the whole refine_transfer-stuff on arbitrary relations *)
(* TODO: For enres-breakdown, we had to do antisymmetry, in order to get TR_top.
  What is the general shape of tr-relations for that, such that we could show equality directly?
*)
lemma RECT_transfer_rel:
  assumes [simp]: "trimono F" "trimono F'"
  assumes TR_top[simp]: "\<And>x. tr x top"
  assumes P_start[simp]: "P x x'"
  assumes IS: "\<And>D D' x x'. \<lbrakk> \<And>x x'. P x x' \<Longrightarrow> tr (D x) (D' x'); P x x'; RECT F = D \<rbrakk> \<Longrightarrow> tr (F D x) (F' D' x')"
  shows "tr (RECT F x) (RECT F' x')"
  unfolding RECT_def 
  apply auto
  apply (rule flatf_gfp_transfer[where tr=tr and P=P])
  apply (auto simp: trimonoD_flatf_ge)  
  apply (rule IS)
  apply (auto simp: RECT_def)
  done
  
lemma RECT_transfer_rel':
  assumes [simp]: "trimono F" "trimono F'"
  assumes TR_top[simp]: "\<And>x. tr x top"
  assumes P_start[simp]: "P x x'"
  assumes IS: "\<And>D D' x x'. \<lbrakk> \<And>x x'. P x x' \<Longrightarrow> tr (D x) (D' x'); P x x' \<rbrakk> \<Longrightarrow> tr (F D x) (F' D' x')"
  shows "tr (RECT F x) (RECT F' x')"
  using RECT_transfer_rel[where tr=tr and P=P,OF assms(1,2,3,4)] IS by blast

end

