theory IICF_HOL_List
imports "../Intf/IICF_List"
begin

context 
begin

private lemma id_take_nth_drop_rl:
  assumes "i<length l"
  assumes "\<And>l1 x l2. \<lbrakk>l=l1@x#l2; i = length l1 \<rbrakk> \<Longrightarrow> P (l1@x#l2)"
  shows "P l" 
  apply (subst id_take_nth_drop[OF assms(1)])
  apply (rule assms(2))
  apply (subst id_take_nth_drop[OF assms(1)])
  apply simp
  apply (simp add: assms(1))
  done


private lemma list_set_entails_aux: 
  shows "list_assn A l li * A x xi \<Longrightarrow>\<^sub>A list_assn A (l[i := x]) (li[i := xi]) * true"
  apply (rule entails_preI)
  apply (clarsimp)
  apply (cases "i < length l"; cases "i < length li"; (sep_auto dest!: list_assn_aux_eqlen_simp;fail)?)
  apply (erule id_take_nth_drop_rl)
  apply (erule id_take_nth_drop_rl)
  apply (sep_auto simp add: list_update_append)
  done

private lemma list_set_hd_tl_aux: 
  "a \<noteq> [] \<Longrightarrow> list_assn R a c \<Longrightarrow>\<^sub>A R (hd a) (hd c) * true"
  "a \<noteq> [] \<Longrightarrow> list_assn R a c \<Longrightarrow>\<^sub>A list_assn R (tl a) (tl c) * true"
  by (cases c; cases a; sep_auto; fail)+

private lemma list_set_last_butlast_aux:
  "a \<noteq> [] \<Longrightarrow> list_assn R a c \<Longrightarrow>\<^sub>A R (last a) (last c) * true"
  "a \<noteq> [] \<Longrightarrow> list_assn R a c \<Longrightarrow>\<^sub>A list_assn R (butlast a) (butlast c) * true"
  by (cases c rule: rev_cases; cases a  rule: rev_cases; sep_auto; fail)+

private lemma swap_decomp_simp[simp]: 
  "swap (l1 @ x # c21' @ xa # l2a) (length l1) (Suc (length l1 + length c21')) = l1@xa#c21'@x#l2a"
  "swap (l1 @ x # c21' @ xa # l2a) (Suc (length l1 + length c21')) (length l1) = l1@xa#c21'@x#l2a"
  by (auto simp: swap_def list_update_append nth_append)

private lemma list_swap_aux: "\<lbrakk>i < length l; j < length l\<rbrakk> \<Longrightarrow> list_assn A l li \<Longrightarrow>\<^sub>A list_assn A (swap l i j) (swap li i j) * true"
  apply (subst list_assn_aux_len; clarsimp)
  apply (cases "i=j"; (sep_auto;fail)?)
  apply (rule id_take_nth_drop_rl[where l=l and i=i]; simp)
  apply (rule id_take_nth_drop_rl[where l=l and i=j]; simp)
  apply (erule list_match_lel_lel; simp)
  apply (split_list_according li l; sep_auto)
  apply (split_list_according li l; sep_auto)
  done
  
private lemma list_rotate1_aux: "list_assn A a c \<Longrightarrow>\<^sub>A list_assn A (rotate1 a) (rotate1 c) * true"  
  by (cases a; cases c; sep_auto)

private lemma list_rev_aux: "list_assn A a c \<Longrightarrow>\<^sub>A list_assn A (rev a) (rev c) * true"
  apply (subst list_assn_aux_len; clarsimp)
  apply (induction rule: list_induct2)
  apply sep_auto
  apply sep_auto
  apply (erule ent_frame_fwd, frame_inference)
  apply sep_auto
  done

lemma mod_starE: 
  assumes "h \<Turnstile> A*B"
  obtains h1 h2 where "h1\<Turnstile>A" "h2\<Turnstile>B"
  using assms by (auto simp: mod_star_conv)

private lemma CONSTRAINT_is_pureE:
  assumes "CONSTRAINT is_pure A"
  obtains R where "A=pure R"
  using assms by (auto simp: is_pure_conv)

private method solve_dbg = 
  ( (elim CONSTRAINT_is_pureE; (simp only: list_assn_pure_conv the_pure_pure)?)?;
    sep_auto 
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp 
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI 
      elim!: mod_starE
      intro: list_set_entails_aux list_set_hd_tl_aux list_set_last_butlast_aux
             list_swap_aux list_rotate1_aux list_rev_aux
    ;
    ((rule entails_preI; sep_auto simp: list_assn_aux_eqlen_simp | (parametricity; simp; fail))?)
  )

private method solve = solve_dbg; fail

(* TODO: Establish sepref_import param mechanism that can handle this! *)

lemma HOL_list_empty_hnr_aux: "(uncurry0 (return op_list_empty), uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a (list_assn A)" by solve
lemma HOL_list_is_empty_hnr[sepref_fr_rules]: "(return \<circ> op_list_is_empty, RETURN \<circ> op_list_is_empty) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn" by solve
lemma HOL_list_prepend_hnr[sepref_fr_rules]: "(uncurry (return \<circ>\<circ> op_list_prepend), uncurry (RETURN \<circ>\<circ> op_list_prepend)) \<in> A\<^sup>d *\<^sub>a (list_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A" by solve
lemma HOL_list_append_hnr[sepref_fr_rules]: "(uncurry (return \<circ>\<circ> op_list_append), uncurry (RETURN \<circ>\<circ> op_list_append)) \<in> (list_assn A)\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a list_assn A"  by solve
lemma HOL_list_concat_hnr[sepref_fr_rules]: "(uncurry (return \<circ>\<circ> op_list_concat), uncurry (RETURN \<circ>\<circ> op_list_concat)) \<in> (list_assn A)\<^sup>d *\<^sub>a (list_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A"  by solve
lemma HOL_list_length_hnr[sepref_fr_rules]: "(return \<circ> op_list_length, RETURN \<circ> op_list_length) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a nat_assn"  by solve
lemma HOL_list_set_hnr[sepref_fr_rules]: "(uncurry2 (return \<circ>\<circ>\<circ> op_list_set), uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in> (list_assn A)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a list_assn A"  by solve
lemma HOL_list_hd_hnr[sepref_fr_rules]: "(return \<circ> op_list_hd, RETURN \<circ> op_list_hd) \<in> [\<lambda>y. y \<noteq> []]\<^sub>a (list_assn R)\<^sup>d \<rightarrow> R"  by solve
lemma HOL_list_tl_hnr[sepref_fr_rules]: "(return \<circ> op_list_tl, RETURN \<circ> op_list_tl) \<in> [\<lambda>y. y \<noteq> []]\<^sub>a (list_assn A)\<^sup>d \<rightarrow> list_assn A"  by solve
lemma HOL_list_last_hnr[sepref_fr_rules]: "(return \<circ> op_list_last, RETURN \<circ> op_list_last) \<in> [\<lambda>y. y \<noteq> []]\<^sub>a (list_assn R)\<^sup>d \<rightarrow> R"  by solve
lemma HOL_list_butlast_hnr[sepref_fr_rules]: "(return \<circ> op_list_butlast, RETURN \<circ> op_list_butlast) \<in> [\<lambda>y. y \<noteq> []]\<^sub>a (list_assn A)\<^sup>d \<rightarrow> list_assn A"  by solve
lemma HOL_list_swap_hnr[sepref_fr_rules]: "(uncurry2 (return \<circ>\<circ>\<circ> op_list_swap), uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_swap))
 \<in> [\<lambda>((a, b), ba). b < length a \<and> ba < length a]\<^sub>a (list_assn A)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> list_assn A" by solve
lemma HOL_list_rotate1_hnr[sepref_fr_rules]: "(return \<circ> op_list_rotate1, RETURN \<circ> op_list_rotate1) \<in> (list_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A" by solve
lemma HOL_list_rev_hnr[sepref_fr_rules]: "(return \<circ> op_list_rev, RETURN \<circ> op_list_rev) \<in> (list_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A" by solve

lemma HOL_list_replicate_hnr[sepref_fr_rules]: "CONSTRAINT is_pure A \<Longrightarrow> (uncurry (return \<circ>\<circ> op_list_replicate), uncurry (RETURN \<circ>\<circ> op_list_replicate)) \<in> nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a list_assn A" by solve
lemma HOL_list_get_hnr[sepref_fr_rules]: "CONSTRAINT is_pure A \<Longrightarrow> (uncurry (return \<circ>\<circ> op_list_get), uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [\<lambda>(a, b). b < length a]\<^sub>a (list_assn A)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> A" by solve

(* TODO: Ad-hoc hack! *)
private lemma bool_by_paramE: "\<lbrakk> a; (a,b)\<in>Id \<rbrakk> \<Longrightarrow> b" by simp
private lemma bool_by_paramE': "\<lbrakk> a; (b,a)\<in>Id \<rbrakk> \<Longrightarrow> b" by simp

lemma HOL_list_contains_hnr[sepref_fr_rules]: "\<lbrakk>CONSTRAINT is_pure A; single_valued (the_pure A); single_valued ((the_pure A)\<inverse>)\<rbrakk>
  \<Longrightarrow> (uncurry (return \<circ>\<circ> op_list_contains), uncurry (RETURN \<circ>\<circ> op_list_contains)) \<in> A\<^sup>k *\<^sub>a (list_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn" 
  apply solve_dbg
  apply (erule bool_by_paramE[where a="_\<in>set _"]) apply parametricity
  apply (erule bool_by_paramE'[where a="_\<in>set _"]) apply parametricity
  done
 

lemmas HOL_list_empty_hnr_mop = HOL_list_empty_hnr_aux[FCOMP mk_mop_rl0_np[OF mop_list_empty_alt]]
lemmas HOL_list_is_empty_hnr_mop[sepref_fr_rules] = HOL_list_is_empty_hnr[FCOMP mk_mop_rl1_np[OF mop_list_is_empty_alt]]
lemmas HOL_list_prepend_hnr_mop[sepref_fr_rules] = HOL_list_prepend_hnr[FCOMP mk_mop_rl2_np[OF mop_list_prepend_alt]]
lemmas HOL_list_append_hnr_mop[sepref_fr_rules] = HOL_list_append_hnr[FCOMP mk_mop_rl2_np[OF mop_list_append_alt]]
lemmas HOL_list_concat_hnr_mop[sepref_fr_rules] = HOL_list_concat_hnr[FCOMP mk_mop_rl2_np[OF mop_list_concat_alt]]
lemmas HOL_list_length_hnr_mop[sepref_fr_rules] = HOL_list_length_hnr[FCOMP mk_mop_rl1_np[OF mop_list_length_alt]]
lemmas HOL_list_set_hnr_mop[sepref_fr_rules] = HOL_list_set_hnr[FCOMP mk_mop_rl3[OF mop_list_set_alt]]
lemmas HOL_list_hd_hnr_mop[sepref_fr_rules] = HOL_list_hd_hnr[FCOMP mk_mop_rl1[OF mop_list_hd_alt]]
lemmas HOL_list_tl_hnr_mop[sepref_fr_rules] = HOL_list_tl_hnr[FCOMP mk_mop_rl1[OF mop_list_tl_alt]]
lemmas HOL_list_last_hnr_mop[sepref_fr_rules] = HOL_list_last_hnr[FCOMP mk_mop_rl1[OF mop_list_last_alt]]
lemmas HOL_list_butlast_hnr_mop[sepref_fr_rules] = HOL_list_butlast_hnr[FCOMP mk_mop_rl1[OF mop_list_butlast_alt]]
lemmas HOL_list_swap_hnr_mop[sepref_fr_rules] = HOL_list_swap_hnr[FCOMP mk_mop_rl3[OF mop_list_swap_alt]]
lemmas HOL_list_rotate1_hnr_mop[sepref_fr_rules] = HOL_list_rotate1_hnr[FCOMP mk_mop_rl1_np[OF mop_list_rotate1_alt]]
lemmas HOL_list_rev_hnr_mop[sepref_fr_rules] = HOL_list_rev_hnr[FCOMP mk_mop_rl1_np[OF mop_list_rev_alt]]
lemmas HOL_list_replicate_hnr_mop[sepref_fr_rules] = HOL_list_replicate_hnr[FCOMP mk_mop_rl2_np[OF mop_list_replicate_alt]]
lemmas HOL_list_get_hnr_mop[sepref_fr_rules] = HOL_list_get_hnr[FCOMP mk_mop_rl2[OF mop_list_get_alt]]
lemmas HOL_list_contains_hnr_mop[sepref_fr_rules] = HOL_list_contains_hnr[FCOMP mk_mop_rl2_np[OF mop_list_contains_alt]]

lemmas HOL_list_empty_hnr = HOL_list_empty_hnr_aux HOL_list_empty_hnr_mop

end

definition [simp]: "op_HOL_list_empty \<equiv> op_list_empty"
interpretation HOL_list: list_custom_empty "list_assn A" "return []" op_HOL_list_empty
  apply unfold_locales
  apply (sep_auto intro!: hfrefI hn_refineI)
  by simp


schematic_goal
  notes [sepref_fr_rules] = HOL_list_empty_hnr
  shows
  "hn_refine (emp) (?c::?'c Heap) ?\<Gamma>' ?R (do {
    x \<leftarrow> RETURN [1,2,3::nat];
    let x2 = op_list_append x 5;
    ASSERT (length x = 4);
    let x = op_list_swap x 1 2;
    x \<leftarrow> mop_list_swap x 1 2;
    RETURN (x@x)
  })"  
    by sepref

end
